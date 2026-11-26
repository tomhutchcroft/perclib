---
{
  "id": "planar-pointwise-lace",
  "title": "Pointwise lace bounds and the spatial asymptotic",
  "subtitle": "Removing two long edges from a planar diagram",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "A planar Fourier bound controls the diagram left after deleting one edge from each outer route. Extracting two long edges then doubles a spatial decay exponent. Combined with the all-order moment estimate, this proves the critical Gaussian asymptotic in sufficiently large dimension.",
  "context": [
    "Nearest-neighbour Bernoulli bond percolation on $\\mathbb Z^d$; $j_c=2dp_c$.",
    "Fourier norms use normalized Haar measure on $\\mathbb T^d$, and $\\langle x\\rangle=\\max\\{1,|x|\\}$.",
    "The dimension threshold is qualitative. The argument does not establish the sharper numerical range in the source."
  ],
  "related": [
    "planar-lace-moments",
    "fourier-spatial-moment-bridge",
    "signed-kernel-gaussian-asymptotics",
    "spatial-convolution-asymptotics",
    "lace-coefficient-diagrams"
  ],
  "sourceIds": [
    "hara-nearest-neighbour-2008",
    "heydenreich-hofstad"
  ],
  "aliases": [
    "separated long lace segments",
    "planar two-edge deletion",
    "qualitative critical spatial asymptotic"
  ],
  "prototypeUses": []
}
---

## The diagram after deleting two edges {#section-deletion}

<p>Let $G$ be one of the order-$N$ expanded diagrams, $N\ge1$, in the <a href="/articles/planar-lace-moments/#section-faces">plane embedding of SJIL</a>. Its outer boundary is a simple cycle, split at $0$ and $x$ into two routes. Each bounded face has at most six edges. The vertices denoted by $a_i$ in the second intermediate block are the only interior vertices; they have degree three and are pairwise nonadjacent.</p>
<p>One more property of the embedding will be useful. Every nonterminal boundary vertex can be joined to the opposite outer route using only interior edges. At either end triangle or a first-type block this is the transverse edge. At a second-type block it is a path through $a_i$. Identifying the zero-length side of that block does not change this property.</p>

<a id="tag-LS5S" data-assertion="proposition" data-title="Deleting one edge from each outer route leaves a uniformly bounded two-root diagram"></a>
<p>Delete an edge $e$ from one outer route and an edge $f$ from the other. Assign a nonnegative kernel $g_h$ to every remaining edge $h$, with Fourier density $A_h\in L^{12}(\mathbb T^d)$. For every $x\in\mathbb Z^d$,</p>
<div class="math-display">$$\sum_{(x_v)_{v\notin\{0,x\}}}\prod_{h=(u,v)\in E(G)\setminus\{e,f\}}g_h(x_v-x_u)
\le\prod_{h\in E(G)\setminus\{e,f\}}\|A_h\|_{12},\qquad x_0=0,\quad x_x=x.$$</div>
<p>The two fixed vertices are distinct vertices of the abstract diagram, even when their spatial positions agree.</p>
<p><em>Proof.</em> Write $H=G-\{e,f\}$. The outer boundary minus $e,f$ consists of two paths, one containing each fixed vertex. Every interior vertex has neighbours on the boundary, so every component of $H$ contains a fixed vertex. Hence $H$ is either connected or has exactly two components.</p>
<p>We next show that deleting any bridge of $H$ cannot produce a component containing neither fixed vertex. Suppose such a component has vertex set $S$, and denote the bridge by $h$. Its edge boundary in $G$ is contained in $\{e,f,h\}$. The component contains a boundary vertex: otherwise it consists of a single interior vertex, whose three incident edges survive deletion of $e,f$ and cannot all be the edge $h$. Its complement also contains boundary vertices, including both fixed vertices. Thus its cut meets the outer cycle in a nonzero even number of edges, necessarily two.</p>
<p>These two cycle edges cut off a boundary interval containing neither $0$ nor $x$. They therefore lie on the same outer route and cannot be the pair $e,f$. It follows that $h$ is a boundary edge, and all of the cut edges of $S$ are boundary edges. But any vertex of the interval has an interior-edge path to the opposite route, which is outside $S$. Such a path must cross the cut on an interior edge, a contradiction.</p>
<p>Consequently, if $H$ is connected, each of its bridges separates $0$ and $x$. If $H$ has two components, each is bridgeless: a bridge would split the component containing its single fixed vertex and leave an unrooted component.</p>
<p>Deleting the boundary edge $e$ merges its incident bounded face with the outer face. If $f$ has the same incident bounded face, it is then a bridge, and its deletion disconnects the graph. Otherwise its deletion merges a second bounded face with the outer face and leaves the graph connected. All other bounded faces retain their original boundaries.</p>
<p>In the disconnected case, apply <a href="/tag/VPUS/">VPUS</a> separately to the two rooted components, using exponent $12$ on each edge. Each surviving face has at most six edges. An isolated fixed vertex contributes one. Multiplication gives the stated bound.</p>
<p>In the connected case, add an auxiliary edge from $0$ to $x$ through the outer face. Give it the kernel $\mathbf1_{\{y=x\}}$, orienting it toward $x$. The new rooted diagram equals the required two-root sum. Every bridge of $H$ separates the endpoints of the auxiliary edge, so lies on a cycle after that edge is added. The new graph is therefore bridgeless. It has the surviving original bounded faces and one new bounded face, with Fourier variable $q_*$. The auxiliary Fourier factor has modulus one.</p>
<p>Use the facial Fourier identity from VPUS. First integrate all the surviving original face variables, holding $q_*$ fixed. Each such face has at most six remaining factors, so Hölder with exponent $12$ removes them at the cost of their norms, independently of $q_*$. Any nonauxiliary factor still present belonged to the boundaries of the two erased faces and to no surviving bounded face. Such edges are precisely the bridges of $H$. There are at most ten: the two erased faces have at most twelve edge occurrences in total, including the two deleted edges. Each remaining factor has argument $q_*$ or $-q_*$. Hölder in $q_*$ therefore bounds their product by the remaining $L^{12}$ norms. The auxiliary factor costs one.</p>
<p>This proves the result for finitely supported kernels. For general kernels apply the positive product Fejér multipliers from VPUS to each $A_h$. They contract the norms, and their nonnegative spatial coefficients increase to $g_h$. Monotone convergence in the two-root sum proves the same bound. The auxiliary kernel is left unchanged.</p>

## Extracting the long edges {#section-pointwise}

<p>Suppose critical clusters are finite almost surely and $\tau_c,\widetilde\tau_c=j_cD*\tau_c$ have Fourier densities $R,S\in L^{12}$. Put</p>
<div class="math-display">$$U=\max\{1,\|R\|_{12}\},\qquad V=\|S\|_{12},\qquad \rho=2U^5V.$$</div>

<a id="tag-8F9A" data-assertion="theorem" data-title="A spatial decay exponent doubles in the full lace coefficient series when the connector norm is small"></a>
<p>Assume $\rho<1$ and, for some $\alpha>0$ and $\Gamma<\infty$,</p>
<div class="math-display">$$\tau_c(x)\le\Gamma\langle x\rangle^{-\alpha}.$$</div>
<p>Set $\Gamma_*=2^\alpha\max\{1,j_c\}\Gamma$. For $N\ge2$ and every $p\le p_c$,</p>
<div class="math-display">$$\Pi_p^{(N)}(x)\le
2\Gamma_*^2U^{12}(2N+1)^{2\alpha+2}\rho^{N-2}\langle x\rangle^{-2\alpha}.$$</div>
<p>In particular, with a finite constant depending on the displayed parameters,</p>
<div class="math-display">$$\sup_{0\le p\le p_c}\sum_{N\ge0}\Pi_p^{(N)}(x)\le C\langle x\rangle^{-2\alpha}.$$</div>
<p><em>Proof.</em> A nearest-neighbour shift satisfies $\langle y-z\rangle\ge\langle y\rangle/2$. Thus both $\tau_c$ and $\widetilde\tau_c$ are bounded by $\Gamma_*\langle y\rangle^{-\alpha}$.</p>
<p>Fix an expanded order-$N$ diagram and a placement of its vertices. Each outer route from $0$ to $x$ has at most $L=2N+1$ edges. The triangle inequality gives an edge of displacement at least $|x|/L$ on each route. Their factors are at most $\Gamma_*L^\alpha\langle x\rangle^{-\alpha}$. This remains true at $x=0$, where any pair of route edges may be chosen. The two chosen edges are distinct. Taking the union over their at most $L^2$ possible positions and dropping the long-edge restrictions gives an upper bound</p>
<div class="math-display">$$\Gamma_*^2L^{2\alpha}\langle x\rangle^{-2\alpha}
\sum_{e\text{ on route }1}\sum_{f\text{ on route }2}\mathcal D_{G-\{e,f\}}(0,x).$$</div>
<p>Apply LS5S to every remaining diagram. If $h\le2$ deleted edges are connectors, the Fourier norms of the remaining edges contribute at most $U^{5N+h}V^{N-h}$. Since $V<1$ and $U\ge1$, this is at most $U^{5N+2}V^{N-2}$ for $N\ge2$. There are $2^{N-1}$ expanded diagrams, and</p>
<div class="math-display">$$2^{N-1}U^{5N+2}V^{N-2}=2U^{12}\rho^{N-2}.$$</div>
<p>This proves the stated estimate at criticality. The witness diagrams at every $p\le p_c$ are bounded by their critical versions, so the same estimate holds uniformly below criticality; no monotonicity of $\Pi_p^{(N)}$ is required. If $V=0$, all connector kernels vanish and all positive-order diagrams are zero, which gives the conclusion directly.</p>
<p>At order one there is a single expanded diagram and at most one connector can be deleted. The same argument bounds it by $\Gamma_*^2 3^{2\alpha+2}U^7\langle x\rangle^{-2\alpha}$. At order zero, BK gives $\Pi_p^{(0)}(x)\le\tau_c(x)^2$ off the origin, while $\Pi_p^{(0)}(0)=0$. The polynomial order factor is summable against $\rho^{N-2}$, proving the full-series bound.</p>

## Closing the spatial argument in large dimension {#section-gaussian}

<a id="tag-KF2I" data-assertion="theorem" data-title="Nearest-neighbour critical percolation has the Gaussian spatial asymptotic in sufficiently large dimension"></a>
<p>There is a finite dimension threshold $d_0$ such that for every $d\ge d_0$, nearest-neighbour bond percolation satisfies</p>
<div class="math-display">$$\tau_c(x)=\frac{A_d}{j_ca_c}\langle x\rangle^{2-d}
+O_d\!\left(\langle x\rangle^{-(d-2+2/d)}\right),\qquad
A_d=\frac{d\,\Gamma(d/2-1)}{2\pi^{d/2}},$$</div>
<p>where</p>
<div class="math-display">$$a_c=1+j_c\sum_x|x|^2\Pi_c(x)>0,\qquad
\Pi_c=\sum_{N\ge0}(-1)^N\Pi_c^{(N)}.$$</div>
<p>Moreover,</p>
<div class="math-display">$$\sup_{0\le p\le p_c}\sum_{N\ge0}\Pi_p^{(N)}(x)
\le C_d\langle x\rangle^{-2(d-2)}.$$</div>
<p><em>Proof.</em> By <a href="/tag/F7N7/">F7N7</a> and <a href="/tag/GIN9/">GIN9</a>, there is a dimension threshold, independent of the moment order, above which the critical Fourier representation, the absolute second moment and the smallness condition $\rho<1$ all hold. Increase that threshold so $d\ge60$.</p>
<p>For this fixed dimension choose the even integer</p>
<div class="math-display">$$M=2\left\lfloor\frac{d-7}{6}\right\rfloor.$$</div>
<p>It satisfies</p>
<div class="math-display">$$3(M+2)<d,\qquad 4M>d+2,\qquad 2M<d-2.$$</div>
<p>Indeed $M\le(d-7)/3$, while the six residue classes of $d$ give $M\ge(d-12)/3$. These bounds imply the three inequalities for $d\ge60$. Starting from the second moment, repeatedly apply <a href="/tag/KOTM/">KOTM</a> with powers of two until a moment of order at least $M$ has been reached. Each input order is less than $M$, so its dimension condition holds. Then apply KOTM at order $M$ itself. The full nonnegative coefficient series has an absolute $2M$th moment. The alternating sum and the effective kernels</p>
<div class="math-display">$$b=\delta_0+\Pi_c,\qquad Q=j_cD*b$$</div>
<p>inherit this moment. Their gap and symmetries are already supplied by the critical Fourier bootstrap.</p>
<p>Apply <a href="/tag/1165/">1165</a> with derivative order $2M<d-2$ to obtain $\tau_c(x)\le C_d\langle x\rangle^{-2M}$. The theorem 8F9A, with $\alpha=2M$, now yields</p>
<div class="math-display">$$|\Pi_c(x)|\le\sum_N\Pi_c^{(N)}(x)\le C_d\langle x\rangle^{-4M}.$$</div>
<p>Since $4M>d+2$, finite-range convolution gives $|Q(x)|\le C_d\langle x\rangle^{-d-2}$. The kernel $Q$ has mass one, finite absolute fourth moment, coordinate symmetries and the quadratic Fourier gap. Thus all hypotheses of the signed-kernel theorem <a href="/tag/OT9N/">OT9N</a> hold. Its signed second moment is</p>
<div class="math-display">$$\sum_x|x|^2Q(x)=1+j_c\sum_x|x|^2\Pi_c(x)=a_c>0.$$</div>
<p>Consequently the inverse Fourier integral $G_c$ of $(1-\widehat Q)^{-1}$ satisfies</p>
<div class="math-display">$$G_c(x)=\frac{A_d}{a_c}\langle x\rangle^{2-d}
+O_d\!\left(\langle x\rangle^{-(d-2+2/d)}\right).$$</div>
<p>Absolute Fubini gives $\tau_c=b*G_c$: the kernel $b$ is summable and the Fourier integrand of $G_c$ is integrable. The mass of $b$ is $1/j_c$. Its pointwise exponent $4M>d+2$ is greater than $d+2/d$, so <a href="/tag/MZ23/">MZ23</a>, with remainder exponent $2/d<1$, transfers the displayed expansion through $b$. This proves the asserted amplitude and error term for $\tau_c$.</p>
<p>The resulting bound $\tau_c(x)\le C_d\langle x\rangle^{2-d}$ allows a second application of 8F9A, now with $\alpha=d-2$. This gives the final coefficient bound uniformly for $p\le p_c$.</p>
<p>The order of the argument avoids a spatial bootstrap assumption: moments give an initial power, two-edge deletion gives a sufficiently fast coefficient tail, and the signed Gaussian theorem gives the critical spatial asymptotic. The condition $d\ge60$ is only an explicit bound for the moment arithmetic. It must be combined with the unspecified thresholds for F7N7 and $\rho<1$; it is not a claim that dimension 60 has been numerically verified.</p>

## Comparison with the source {#section-source}

<p>Hara's Section 3.5 controls two long segments through a more economical spatial diagram reduction. The deletion lemma above supplies an independent planar Fourier reduction and closes the qualitative sufficiently-high-dimensional argument left open after <a href="/articles/planar-lace-moments/">the moment estimate</a>. Its use of $L^{12}$ norms and two-edge deletion sacrifices the source's sharper dimension range. Fractional-order estimates and numerical dimension thresholds remain separate. These are written proofs, with no new Lean verification or source erratum asserted.</p>

## Weighted convolutions after the spatial theorem {#section-fractional-followup}

<p>The coefficient tail in KF2I supplies every absolute moment of order less than $d-4$. Together with the critical Fourier gap, <a href="/tag/ODMM/">ODMM</a> now gives Fourier identities for real-weighted bubble, triangle and higher convolution sums whenever the total power-counting exponent is less than $d$. The <a href="/articles/fractional-fourier-weights/">fractional construction</a> distinguishes an absolute coordinate power from an ordinary odd derivative and retains the strict endpoint restrictions.</p>

## Closing the argument with a real moment {#section-real-closure}

<p>The even order chosen in KF2I can now be replaced by a real order. This improves the dimension arithmetic inside that proof. It does not determine the dimension above which its probabilistic hypotheses hold.</p>

<a id="tag-QKEC" data-assertion="theorem" data-title="The spatial asymptotic follows above dimension thirty once the critical Fourier and connector hypotheses hold"></a>
<p>Consider nearest-neighbour bond percolation on $\mathbb Z^d$, with $d>30$. Suppose critical clusters are finite almost surely and the critical two-point function has the inverse Fourier representation</p>
<div class="math-display">$$R=\frac{\widehat b}{1-\widehat Q},\qquad
b=\delta_0+\Pi_c,\qquad Q=j_cD*b,\qquad
\Pi_c=\sum_{N\ge0}(-1)^N\Pi_c^{(N)}.$$</div>
<p>Assume $b,Q$ have finite absolute second moments, the coordinate reflection and permutation symmetries, $\sum_xQ(x)=1$, and $1-\widehat Q(k)\ge c|k|^2$ for some $c>0$. With $U,V,\rho$ as above, suppose $\rho<1$. Then, with $A_d,a_c$ as in KF2I and $a_c>0$,</p>
<div class="math-display">$$\tau_c(x)=\frac{A_d}{j_ca_c}\langle x\rangle^{2-d}
+O_d\!\left(\langle x\rangle^{-(d-2+2/d)}\right),$$</div>
<p>and</p>
<div class="math-display">$$\sup_{0\le p\le p_c}\sum_{N\ge0}\Pi_p^{(N)}(x)
\le C_d\langle x\rangle^{-2(d-2)}.$$</div>
<p><em>Proof.</em> Choose a real $K$ in the interval</p>
<div class="math-display">$$\frac{d+2}{4}<K<\frac{d-6}{3}.$$</div>
<p>The interval has length $(d-30)/12>0$. By <a href="/tag/6N01/">6N01</a>, the full coefficient series has an absolute $2K$th moment and $\tau_c(x)\le C_d\langle x\rangle^{-2K}$. Indeed $2K<2(d-6)/3$, and this lies below $d-2$. Apply 8F9A with $\alpha=2K$ to obtain</p>
<div class="math-display">$$\sup_{p\le p_c}\sum_N\Pi_p^{(N)}(x)\le C_d\langle x\rangle^{-4K},\qquad 4K>d+2.$$</div>
<p>Thus $b$ and its finite-range convolution $Q$ have the pointwise tail needed in OT9N. They also have finite absolute fourth moments, since $2K>(d+2)/2>4$. The mass and symmetries give</p>
<div class="math-display">$$\sum_x|x|^2Q(x)=1+j_c\sum_x|x|^2\Pi_c(x)=a_c.$$</div>
<p>The gap implies $a_c>0$ by the quadratic Taylor expansion along a coordinate axis. OT9N therefore gives the Gaussian expansion, with remainder exponent $2/d$, for the inverse transform of $(1-\widehat Q)^{-1}$. Convolution with $b$ is justified by absolute Fubini. Its mass is $1/j_c$, and its pointwise exponent $4K>d+2>d+2/d$ allows MZ23 to transfer that expansion to $\tau_c$ with the stated amplitude. Finally apply 8F9A once more with $\alpha=d-2$.</p>
<p>For example, at the first integer dimension permitted by this arithmetic, $d=31$, one may take $K=199/24$. The input orders $2,4,8$ give moments $4,8,16$; PCOC then gives the moment $2K=199/12$. The inequalities are strict: $3(K+2)=247/8<31$ and $4K=199/6>33$. This checks the arithmetic only. Neither the Fourier bootstrap nor $\rho<1$ has been numerically verified here at $d=31$.</p>
<p>The original qualitative theorem KF2I and all its tagged content remain unchanged. QKEC records a stronger conditional analytic implication. The sufficiently-large-dimension conclusion still follows from F7N7 and the connector estimate in GIN9, with an unspecified threshold.</p>

## Counting the remaining bridges {#section-three-bridges}

<p>The bound of ten factors in LS5S counts every edge of the erased faces. Most of these factors have already been removed by the surviving face integrations. The actual bridge count is smaller.</p>

<a id="tag-RCF3" data-assertion="proposition" data-title="Two outer-edge deletions leave at most three bridges and require only sixth Fourier norms"></a>
<p>In the two-root strip of LS5S, deletion of one edge from each outer route leaves at most three bridges. For every $6\le q<\infty$, its two-root sum is bounded by the product of the $L^q$ norms of its remaining Fourier densities.</p>
<p>Consequently, the pointwise estimates of 8F9A hold with $U,V,\rho$ replaced by $U_9,V_9,\rho_9$, provided $\rho_9<1$ and $\tau_c(y)\le\Gamma\langle y\rangle^{-\alpha}$. In particular, with $\Gamma_*=2^\alpha\max\{1,j_c\}\Gamma$,</p>
<div class="math-display">$$\Pi_p^{(N)}(x)\le
2\Gamma_*^2U_9^{12}(2N+1)^{2\alpha+2}\rho_9^{N-2}\langle x\rangle^{-2\alpha}
\qquad(N\ge2,\ p\le p_c),$$</div>
<p>and $\sup_{p\le p_c}\sum_N\Pi_p^{(N)}(x)\le C\langle x\rangle^{-2\alpha}$.</p>
<p><em>Proof.</em> Each bounded face of the original strip has at most two edges on the outer boundary. Distinct bounded faces share at most one edge. Both facts follow directly from the block description: a block face meets either neighbouring connector face in one edge and no other block face; two connector faces can share only $(a_i,t_i)$, when the block between them is of the second type.</p>
<p>The cut argument in LS5S shows that a disconnected remainder consists of two bridgeless rooted components. Otherwise the two deleted edges erase distinct bounded faces $F_1,F_2$, and every bridge separates the roots. An edge surviving no bounded-face integration must either be an outer edge incident to one of $F_1,F_2$, or an edge shared by them. The first class contains at most $2+2-2=2$ edges: the two deleted edges were outer edges. The second contains at most one. These are exactly the bridges, because an edge of a connected plane graph is a bridge precisely when its two incident faces coincide. This proves the count.</p>
<p>For the norm bound, use the proof of LS5S. Each surviving original face has at most six factors, so its integration uses at most $6/q\le1$ of the Hölder budget. In the connected case the auxiliary face is left with at most three factors and a factor of modulus one; $3/q\le1$ suffices there. In the disconnected case apply the rooted facial bound separately to the two components. Positive Fejér smoothing and monotone convergence remove the finite-support restriction.</p>
<p>Now take $q=9$ and extract one long edge from each outer route, as in 8F9A. For $N\ge2$ at least $N-2$ connector factors remain, and the unchanged edge counts give $2U_9^{12}\rho_9^{N-2}$ after summing the expanded diagrams. The route lengths and number of marked pairs give $(2N+1)^{2\alpha+2}$. At order one the same argument gives $\Gamma_*^2 3^{2\alpha+2}U_9^7\langle x\rangle^{-2\alpha}$; order zero is bounded by BK. Summing in $N$ proves the full-series estimate. The zero-connector case and domination of lower-parameter witness diagrams are as in 8F9A.</p>

## Conditional spatial closure above dimension eighteen {#section-ninth-closure}

<a id="tag-CP1T" data-assertion="theorem" data-title="Ninth-norm connector smallness closes the critical spatial argument in every integer dimension at least nineteen"></a>
<p>Consider nearest-neighbour bond percolation on $\mathbb Z^d$, with $d>18$. Suppose critical clusters are finite almost surely and</p>
<div class="math-display">$$\tau_c(x)=\int e^{-ik\cdot x}R(k)\,dk,\qquad
R=\frac{\widehat b}{1-\widehat Q},\qquad
b=\delta_0+\Pi_c,\qquad Q=j_cD*b,\qquad
\Pi_c=\sum_{N\ge0}(-1)^N\Pi_c^{(N)}.$$</div>
<p>Assume $b,Q$ have finite absolute second moments, the coordinate reflection and permutation symmetries, $\sum_xQ(x)=1$, and $1-\widehat Q(k)\ge c|k|^2$ for some $c>0$. If $\rho_9=2U_9^5V_9<1$, then</p>
<div class="math-display">$$\tau_c(x)=\frac{A_d}{j_ca_c}\langle x\rangle^{2-d}
+O_d\!\left(\langle x\rangle^{-(d-2+2/d)}\right),\qquad
\sup_{0\le p\le p_c}\sum_{N\ge0}\Pi_p^{(N)}(x)
\le C_d\langle x\rangle^{-2(d-2)},$$</div>
<p>where $A_d=d\,\Gamma(d/2-1)/(2\pi^{d/2})$ and $a_c=1+j_c\sum_x|x|^2\Pi_c(x)>0$.</p>
<p><em>Proof.</em> Choose</p>
<div class="math-display">$$\frac{d+2}{4}<K<\frac{7d}{18}-2.$$</div>
<p>The interval has length $5(d-18)/36>0$. The moment range in 5T90 gives an absolute $2K$th moment of the full coefficient series and $\tau_c(x)\le C\langle x\rangle^{-2K}$. The hypotheses for RCF3 hold, so it gives the coefficient tail $\sum_N\Pi_c^{(N)}(x)\le C\langle x\rangle^{-4K}$, where $4K>d+2$.</p>
<p>The kernels $b,Q$ inherit this tail and have finite absolute fourth moments, because $2K>(d+2)/2>4$. Their mass, symmetries and quadratic expansion give</p>
<div class="math-display">$$\sum_x|x|^2Q(x)=1+j_c\sum_x|x|^2\Pi_c(x)=a_c>0.$$</div>
<p>The strict positivity follows from the gap along a coordinate axis. OT9N therefore gives the Gaussian expansion with remainder exponent $2/d$ for the inverse transform of $(1-\widehat Q)^{-1}$. Absolute Fubini identifies its convolution with $b$ as $\tau_c$. The identity $\sum Q=j_c\sum b=1$ gives the mass $1/j_c$ of $b$, and $4K>d+2>d+2/d$ allows MZ23 to transfer the expansion with the stated amplitude. A second application of RCF3, now with $\alpha=d-2$, proves the final coefficient bound.</p>
<p>For the arithmetic at $d=19$, take $K=383/72$. The input orders two and four give moments four and eight, after which 5T90 applies at $K$. Here $(18/7)(K+2)=527/28<19$ and $4K=383/18>21$. This is a conditional implication, not a numerical verification of the hypotheses at dimension nineteen. The critical Fourier input and $\rho_9<1$ still need their own estimates. In sufficiently large dimension they follow from F7N7 and the connector bound in GIN9, since the ninth norms are at most the twelfth norms on normalized Haar measure.</p>

<p>The refinement comes from the explicit strip geometry, not from an assumed spatial decay or a new source correction. Hara's finer spatial decompositions and their numerical smallness constants remain separate source correspondence work. The earlier statements KF2I and QKEC are preserved.</p>

## The pointwise estimate with sixth norms {#section-sixth-norms}

<p>The moment estimate B0RG no longer needs ninth norms. We can therefore use the endpoint $q=6$ of the two-root bound RCF3 for the pointwise step. Write</p>
<div class="math-display">$$U_6=\max\{1,\|R\|_6\},\qquad V_6=\|S\|_6,\qquad
S=j_c\widehat D R,\qquad \rho_6=2U_6^5V_6.$$</div>

<a id="tag-634L" data-assertion="theorem" data-title="Sixth-norm connector smallness doubles a spatial decay exponent in every lace order"></a>
<p>Suppose critical clusters are finite almost surely, $R,S\in L^6$, $\rho_6<1$, and $\tau_c(x)\le\Gamma\langle x\rangle^{-a}$ for some $a>0$. Put $\Gamma_*=2^a\max\{1,j_c\}\Gamma$. For $N\ge2$ and every $p\le p_c$,</p>
<div class="math-display">$$\Pi_p^{(N)}(x)\le
2\Gamma_*^2U_6^{12}(2N+1)^{2a+2}\rho_6^{N-2}\langle x\rangle^{-2a}.$$</div>
<p>The orders zero and one satisfy</p>
<div class="math-display">$$\Pi_p^{(0)}(x)\le\Gamma^2\langle x\rangle^{-2a},\qquad
\Pi_p^{(1)}(x)\le\Gamma_*^2 3^{2a+2}U_6^6\langle x\rangle^{-2a}.$$</div>
<p>In particular, $\sup_{p\le p_c}\sum_N\Pi_p^{(N)}(x)\le C\langle x\rangle^{-2a}$.</p>
<p><em>Proof.</em> The nearest-neighbour shift bound used in 8F9A bounds both edge kernels by $\Gamma_*\langle y\rangle^{-a}$. Extract one long edge from each outer route. For a specified pair of positions, RCF3 at $q=6$ bounds the remaining two-root diagram by the product of its sixth norms. The facewise inequalities allow equality at $q=6$; the positive Fejér approximation therefore gives the bound at this endpoint as well.</p>
<p>An order-$N$ diagram has $5N+2$ ordinary edges and $N$ connector edges. If $h$ of the two removed edges are connectors, the remaining norm product is at most $U_6^{5N+h}V_6^{N-h}$. For $N\ge2$, use $h\le2$, $U_6\ge1$ and $V_6<1$, then sum the $2^{N-1}$ expanded diagrams:</p>
<div class="math-display">$$2^{N-1}U_6^{5N+h}V_6^{N-h}
\le 2U_6^{12}\rho_6^{N-2}.$$</div>
<p>The two extracted factors and the at most $(2N+1)^2$ choices give the remaining factor $\Gamma_*^2(2N+1)^{2a+2}\langle x\rangle^{-2a}$. At order one, $h\le1$ gives $U_6^{5+h}V_6^{1-h}\le U_6^6$; there is only one expanded diagram. Order zero follows from BK, including its vanishing value at the origin. If $V_6=0$, all positive-order diagrams vanish, so that case is immediate. Critical witness diagrams dominate those at lower parameters. Finally the polynomial factors in $N$ are summable against the geometric factor $\rho_6^{N-2}$.</p>

## Conditional spatial closure above dimension fourteen {#section-sixth-closure}

<a id="tag-FWHO" data-assertion="theorem" data-title="Sixth-norm smallness and the critical Fourier hypotheses give the Gaussian asymptotic above dimension fourteen"></a>
<p>Consider nearest-neighbour bond percolation on $\mathbb Z^d$, with $d>14$. Suppose critical clusters are finite almost surely and</p>
<div class="math-display">$$\tau_c(x)=\int e^{-ik\cdot x}R(k)\,dk,\qquad
R=\frac{\widehat b}{1-\widehat Q},\qquad b=\delta_0+\Pi_c,\qquad
Q=j_cD*b,\qquad \Pi_c=\sum_{N\ge0}(-1)^N\Pi_c^{(N)}.$$</div>
<p>Assume $b,Q$ have finite absolute second moments, coordinate reflection and permutation symmetries, $\sum_xQ(x)=1$, and $1-\widehat Q(k)\ge c|k|^2$ for some $c>0$. If $\rho_6<1$, then, with $A_d$ as above,</p>
<div class="math-display">$$\begin{aligned}
\tau_c(x)&=\frac{A_d}{j_ca_c}\langle x\rangle^{2-d}
+O_d\!\left(\langle x\rangle^{-(d-2+4/(d+2))}\right),\\
a_c&=1+j_c\sum_x|x|^2\Pi_c(x)>0,\\
\sup_{0\le p\le p_c}\sum_{N\ge0}\Pi_p^{(N)}(x)&\le C_d\langle x\rangle^{-2(d-2)}.
\end{aligned}$$</div>
<p>Consequently, for every real $0\le s<d-4$, the full coefficient series is uniformly summable with weight $1+|x|^s$ and</p>
<div class="math-display">$$\sum_{N\ge0}\sum_x(1+|x|^s)
\left|\Pi_p^{(N)}(x)-\Pi_c^{(N)}(x)\right|\longrightarrow0
\qquad(p\uparrow p_c).$$</div>
<p>At $s=0$ use a constant weight. No Gaussian spatial estimate is assumed.</p>
<p><em>Proof.</em> The quadratic gap and bounded numerators put $R,S$ in $L^6$, since $d>12$. The nonnegative convolution identity and Hölder give</p>
<div class="math-display">$$\Delta\le\|R\|_6^3,\qquad
T\le\|R\|_6^2\|S\|_6,\qquad
r=2T\Delta\le\rho_6<1.$$</div>
<p>Choose a real exponent $a$ with</p>
<div class="math-display">$$\frac{d+2}{2}<a<d-6.$$</div>
<p>The interval has length $(d-14)/2>0$. B0RG gives an absolute $a$th moment of the full coefficient series and the spatial bound $\tau_c(x)\le C_d\langle x\rangle^{-a}$. Applying 634L yields a pointwise bound $C_d\langle x\rangle^{-2a}$ for that series. Since $2a>d+2$, both $b$ and its finite-range convolution $Q$ have the tail required in the signed-kernel theorem. They have finite absolute fourth moments as well, because $a>4$.</p>
<p>The mass and symmetries give</p>
<div class="math-display">$$\sum_x|x|^2Q(x)=j_c\sum_y(1+|y|^2)b(y)
=1+j_c\sum_y|y|^2\Pi_c(y)=a_c.$$</div>
<p>The quadratic expansion along a coordinate axis and the gap imply $a_c>0$. Apply <a href="/tag/7QGG/">7QGG</a> to $Q$, with its absolute fourth moment. Its Green function has amplitude $A_d/a_c$ and remainder exponent $\beta=4/(d+2)$. Absolute Fubini identifies $\tau_c$ with its convolution by $b$. Now $\sum b=1/j_c$ and $2a>d+2>d+\beta$, so MZ23 transfers this expansion with amplitude $A_d/(j_ca_c)$. This proves the first assertion. Apply 634L again, with $a=d-2$, to obtain the stated coefficient tail.</p>
<p>For the weighted assertions, retain the order-by-order bounds from that last application. Their spatial factor is $\langle x\rangle^{-2(d-2)}$, which is summable with weight $1+|x|^s$ exactly in the asserted strict range $s<d-4$. Their order factor is a polynomial times $\rho_6^{N-2}$, so the joint sum is finite uniformly in $p$. At fixed order and bond tuple the cutting events stabilize in the uniform-edge coupling, since the relevant critical clusters are finite. Dominated convergence, first in the witness sums and then in the joint weighted sum, proves the displayed continuity. No monotonicity of individual lace coefficients is used.</p>
<p>For example, at $d=15$ take $a=35/4$ and input moment $K=a/2=35/8$. The inputs two and four first give moments four and eight; SL9H then applies at $K$, since $2K+6=59/4<15$. The resulting coefficient exponent is $2a=35/2>17=d+2$. The Green remainder exponent is $4/17$.</p>
<p>These inequalities check the conditional analytic argument at dimension fifteen. They do not verify its critical Fourier or smallness hypotheses there. The sixth-norm condition is implied by the earlier ninth-norm condition on normalized Haar measure, and holds in sufficiently large dimension by F7N7 and GIN9. No numerical percolation threshold or new source erratum is asserted. The previous tagged statements are unchanged.</p>
