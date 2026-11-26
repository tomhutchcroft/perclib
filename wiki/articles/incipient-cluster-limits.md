---
{
  "id": "incipient-cluster-limits",
  "title": "Incipient-cluster limits",
  "subtitle": "Cylinder convergence, infinite support and two-point bounds",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "Subsequential conditioning limits on the lattice have an infinite root cluster. Susceptibility bias and distant-point conditioning give the same two-point upper bound under explicit inputs, without assuming that cylinder convergence extends to every connection event.",
  "context": [
    "Nearest-neighbour independent bond percolation on $\\mathbb Z^d$.",
    "Limits are first taken on events determined by finitely many bonds.",
    "Existence of a unique percolation IIC and equality of its different constructions require additional model-specific arguments."
  ],
  "related": [
    "size-biased-laws",
    "critical-arm-bounds",
    "spatial-convolution-asymptotics",
    "tree-graph"
  ],
  "sourceIds": [
    "heydenreich-hofstad"
  ],
  "aliases": [
    "IIC",
    "incipient infinite cluster",
    "susceptibility-biased percolation"
  ],
  "prototypeUses": []
}
---

## Cylinder limits and an infinite root cluster {#section-limits}

<p>Write $C(0)$ for the open cluster of the origin, $\chi(p)=\mathbb E_p|C(0)|$, and $\Lambda_R=[-R,R]^d\cap\mathbb Z^d$. When $\chi(p)<\infty$, the cluster-volume-biased law is</p>
<div class="math-display">$$Q_p(E)=\frac{\mathbb E_p[|C(0)|\mathbf1_E]}{\chi(p)}
=\frac{\sum_x\mathbb P_p(E\cap\{0\leftrightarrow x\})}{\chi(p)}.$$</div>
<p>This is the <a href="/tag/6L9Z/">size-biased law</a>; Tonelli gives the second formula and $Q_p$ is a probability measure.</p>
<p>The existing <a href="/tag/E22E/">compactness and escape theorem</a> applies to three constructions: $Q_{p_n}$ with finite $\chi(p_n)\to\infty$; conditioning at a fixed parameter on $0\leftrightarrow x_n$ with $|x_n|\to\infty$; and conditioning on a connection to box boundaries whose radii tend to infinity. Every sequence has a subsequence converging on cylinders, and every limiting measure gives the root an infinite cluster. Cylinder probabilities determine the limiting measure, but compactness does not identify different subsequences or constructions.</p>
<p>For the critical nearest-neighbour and spread-out models satisfying two-sided spatial two-point bounds in $d>6$, the later <a href="/tag/Q7E9/">distant-set IIC theorem</a> supplies a common distant-point, arm and supercritical-conditioning limit as a cited input. Its proof is not supplied by compactness, and identifying susceptibility bias is a further step. The two upper-bound arguments below apply to the relevant cylinder limits without assuming that a noncylinder connection event has convergent probabilities.</p>

## A two-point bound from susceptibility bias {#section-biased-bound}

<a id="tag-N20X" data-assertion="theorem" data-title="Every susceptibility-biased cylinder limit obeys the critical bubble two-point bound"></a>
<p>Suppose $p_n\uparrow p_*$, $\chi(p_n)<\infty$, $\chi(p_n)\to\infty$, and $Q_{p_n}$ converges on cylinder events to $\mu$. Write $\tau_p(x)=\mathbb P_p(0\leftrightarrow x)$. Then, with an extended nonnegative sum allowed,</p>
<div class="math-display">$$\mu(0\leftrightarrow y)\le (\tau_{p_*}*\tau_{p_*})(y).$$</div>
<p>If $d>4$ and $\tau_{p_*}(x)\le\Gamma\langle x\rangle^{2-d}$, this gives</p>
<div class="math-display">$$\mu(0\leftrightarrow y)\le C_d\Gamma^2\langle y\rangle^{4-d}.$$</div>
<p><em>Proof.</em> The <a href="/tag/L82Q/">three-point tree-graph bound</a>, translation invariance and Tonelli give</p>
<div class="math-display">$$\begin{aligned}
Q_p(0\leftrightarrow y)
&\le\frac1{\chi(p)}\sum_{x,z}\tau_p(z)\tau_p(y-z)\tau_p(x-z)\\
&=\sum_z\tau_p(z)\tau_p(y-z)
\le(\tau_{p_*}*\tau_{p_*})(y)\qquad(p\le p_*).
\end{aligned}$$</div>
<p>Only the passage to the limit needs care. Let $E_R$ be the event that a path from $0$ to $y$ lies inside $\Lambda_R$. For $R$ large enough to contain $y$, this is a cylinder event and $E_R\uparrow\{0\leftrightarrow y\}$. Therefore</p>
<div class="math-display">$$\mu(E_R)=\lim_nQ_{p_n}(E_R)
\le(\tau_{p_*}*\tau_{p_*})(y).$$</div>
<p>Take $R\to\infty$ using continuity from below under the single measure $\mu$. The power bound follows from <a href="/tag/IDIL/">IDIL</a> with both exponents equal to $d-2$.</p>
<p>No equality between $\mu(0\leftrightarrow y)$ and $\lim_nQ_{p_n}(0\leftrightarrow y)$ is needed or proved here. Cylinder convergence alone does not justify that equality. This finite-box argument repairs the upper-bound proof at <a href="/errata/heydenreich-hofstad/#iic-noncylinder-limit">the provisional entry for (12.2.6)</a>.</p>

## A two-point bound from distant-point conditioning {#section-point-bound}

<a id="tag-G86R" data-assertion="theorem" data-title="Distant-point cylinder limits satisfy the same bubble bound under a spatial two-point equivalent"></a>
<p>Let $d>4$ and suppose, at a fixed parameter $p$,</p>
<div class="math-display">$$\tau(x)=\tau_p(x)=A|x|^{2-d}+o(|x|^{2-d})\qquad(|x|\to\infty),\quad A>0.$$</div>
<p>Let $|x_n|\to\infty$ and suppose $\mathbb P_p(\,\cdot\mid0\leftrightarrow x_n)$ converges on cylinders to $\nu$. Then</p>
<div class="math-display">$$\nu(0\leftrightarrow y)\le(\tau*\tau)(y)\le C\langle y\rangle^{4-d}.$$</div>
<p><em>Proof.</em> Put $s=d-2$. The asymptotic supplies a global bound $\tau(z)\le C\langle z\rangle^{-s}$ and a lower bound $\tau(x)\ge c|x|^{-s}$ for large $x$. For each fixed $y$, the tree-graph bound gives</p>
<div class="math-display">$$\mathbb P_p(0\leftrightarrow y\mid0\leftrightarrow x)
\le\sum_z\tau(z)\tau(y-z)\frac{\tau(x-z)}{\tau(x)}.$$</div>
<p>We show that the sum on the right tends to $(\tau*\tau)(y)$. For each fixed $z$, the ratio tends to one. Also $w_y(z)=\tau(z)\tau(y-z)$ is summable since $d>4$.</p>
<p>For the tail, put $R=|x|$ and split at $|x-z|=R/2$. On $|x-z|\ge R/2$ the ratio is bounded by a constant independent of $x,z$, so the contribution from $|z|>L$ is at most $C\sum_{|z|>L}w_y(z)$. On $|x-z|<R/2$, take $R>4|y|+4$. Then $|z|\ge R/2$ and $|z-y|\ge R/4$, and shell counting gives</p>
<div class="math-display">$$\sum_{|x-z|<R/2}w_y(z)\frac{\tau(x-z)}{\tau(x)}
\le C R^{-s}\sum_{|u|<R/2}\langle u\rangle^{-s}
\le C R^{4-d}\longrightarrow0.$$</div>
<p>First let $x\to\infty$ with $L$ fixed, then let $L\to\infty$. This proves convergence of the whole diagram. Apply its bound to the cylinder event $E_R=\{0\leftrightarrow y\text{ inside }\Lambda_R\}$, pass to the conditioning limit, then let the box radius increase. The last power bound again follows from IDIL.</p>
<p>This supplies Exercise 12.1 under the stated spatial equivalent. It does not prove that the distant-point limit exists without passing to a subsequence, or that it equals the susceptibility-biased limit.</p>

## The branching-process comparison {#section-tree-comparison}

<p>The branching-process part of Chapter 12 is already supplied by the <a href="/tag/SBWK/">distant-survival size-bias argument</a>: for a critical nondegenerate Galton–Watson process of finite variance, its restriction to the first $m$ generations has limiting density $Z_m$. The <a href="/tag/XCA8/">martingale consistency</a>, <a href="/tag/RMFH/">explicit spine construction</a> and <a href="/tag/SYJ4/">total-variation estimate</a> give existence and the equivalent size-biased limiting scheme. The unique infinite genealogical ray follows because every ordinary tree grafted onto the spine dies out. These are tree results; one-endedness of the percolation IIC is a separate assertion.</p>
<p>The <a href="/coverage/sources/heydenreich-hofstad-2017-iic/">chapter reading map</a> keeps the model-specific lace construction, equality of the percolation limits, one-endedness and the lower two-point bound separate from the deductions proved here.</p>


## Keeping the intrinsic paths short {#section-short-tree}

<p>Write $B(r)=\{y:d_\omega(0,y)\le r\}$ for the open intrinsic ball, and set</p>
<div class="math-display">$$\tau_{p,r}(x)=\mathbb P_p(x\in B(r)),\qquad
s_p(r)=\sum_x\tau_{p,r}(x)=\mathbb E_p|B(r)|.$$</div>
<p>On the nearest-neighbour lattice, $B(r)$ lies in the deterministic radius-$r$ ball. Its size and all its moments are therefore bounded cylinder functions for each fixed integer $r$.</p>

<a id="tag-0HRJ" data-assertion="theorem" data-title="A short-path tree diagram bounds every intrinsic-ball moment under susceptibility bias"></a>
<p>For nearest-neighbour independent bond percolation on $\mathbb Z^d$, suppose $\chi(p)<\infty$. For every integer $k\ge1$ and $r\ge0$,</p>
<div class="math-display">$$\mathbb E_p\bigl[|C(0)|\,|B(r)|^k\bigr]
\le(2k-1)!!\,\chi(p)\,s_p(r)^{2k},\qquad
\mathbb E_{Q_p}|B(r)|^k\le(2k-1)!!\,s_p(r)^{2k}.$$</div>
<p><em>Proof.</em> Fix $y_1,\ldots,y_k,x$. On the event that all $y_i$ lie in $B(r)$ and $0\leftrightarrow x$, choose open paths of length at most $r$ from zero to each $y_i$. Their union is a finite connected graph. Every vertex in that union has distance at most $r$ from zero within the union, so a breadth-first spanning tree has height at most $r$. Prune it to retain the marked vertices and the attachment point described next.</p>
<p>Take an open path from $x$ to the union and stop at its first hit $a$. This path has no other vertex in the union; if $x$ already belongs to the union, use the empty path. Adjoin it to the breadth-first tree. All paths from zero to $y_i$ in the resulting tree still have length at most $r$, and the added path is its only unrestricted branch.</p>
<p>Apply the reduction in <a href="/tag/AFH6/">the multipoint tree-graph proof</a>: attach labelled leaves at zero, $y_1,\ldots,y_k,x$, suppress unlabelled vertices of degree two, and split higher-degree vertices with empty paths. This gives a leaf-labelled trivalent tree with $2k+1$ edges. The edge incident to the distinguished leaf $x$ may carry a long path. Every other nonempty edge carries an ancestor-to-descendant segment of the breadth-first tree, hence a path of length at most $r$. Empty paths also satisfy this bound. The nonempty witnesses have pairwise disjoint edge sets.</p>
<p>For a fixed tree shape and positions of its $k$ internal vertices, BK therefore bounds the probability by one unrestricted factor $\tau_p(x-z)$, where $z$ is the neighbour of the distinguished leaf, and $2k$ factors of the form $\tau_{p,r}(v-u)$. This remains valid when marked positions coincide. The short-path events are increasing and have finite witnesses, so the finite-coordinate BK bound passes through edge exhaustion.</p>
<p>Sum over $x,y_1,\ldots,y_k$ and all internal positions. The $x$ sum is $\chi(p)$ by translation invariance. After removing that leaf, the remaining graph is a tree with $2k$ edges. Successively sum a leaf position other than the fixed root and delete its edge; each sum is $s_p(r)$. Thus each shape contributes $\chi(p)s_p(r)^{2k}$. There are <a href="/tag/SO5J/">$(2k-1)!!$ shapes</a> with these $k+2$ leaf labels. Tonelli identifies the left side as the mixed moment in the statement. Dividing by $\chi(p)$ gives the biased bound.</p>
<p>The breadth-first choice is needed before reducing the tree: an arbitrary spanning tree of the short paths could lengthen a route to a marked vertex. The proof retains edge-disjoint short witnesses, rather than assuming that a usual unrestricted tree diagram automatically has the desired distance bounds.</p>

## Passing the moments to cylinder limits {#section-intrinsic-limit-moments}

<a id="tag-KIGU" data-assertion="theorem" data-title="Susceptibility-biased and distant-point cylinder limits inherit intrinsic-ball moment bounds"></a>
<p>Let $p_j\to p_*$, with $\chi(p_j)<\infty$ and $\chi(p_j)\to\infty$, and let $Q_{p_j}$ converge on cylinders to $\mu$. Then, for every integer $k\ge1$ and $r\ge0$,</p>
<div class="math-display">$$\mathbb E_\mu|B(r)|^k\le(2k-1)!!\,s_{p_*}(r)^{2k}.$$</div>
<p>The same conclusion holds for a cylinder limit $\nu$ of $\mathbb P_{p_*}(\,\cdot\mid0\leftrightarrow x_j)$, where $|x_j|\to\infty$ and $\tau_{p_*}(x_j)>0$, provided</p>
<div class="math-display">$$\frac{\tau_{p_*}(x_j-z)}{\tau_{p_*}(x_j)}\longrightarrow1
\quad\text{for each fixed }z\in\mathbb Z^d.$$</div>
<p>In either construction the limiting root cluster is infinite almost surely. The conclusions hold for every subsequential cylinder limit meeting these hypotheses; no identification of the two constructions is assumed.</p>
<p><em>Proof.</em> For fixed $r$, the function $|B(r)|^k$ is bounded and depends on finitely many bonds. Its expectation thus converges under cylinder convergence. Also $s_p(r)$ is a polynomial in $p$, since it is the expectation of a finite cylinder function. Apply 0HRJ and let $j\to\infty$ to obtain the first assertion. Monotonicity of the parameter sequence is unnecessary.</p>
<p>For distant-point conditioning, use the short-path diagram in the proof of 0HRJ, keep the distinguished endpoint fixed at $x_j$, and divide by $\tau_{p_*}(x_j)$. Its unrestricted factor is now</p>
<div class="math-display">$$\frac{\tau_{p_*}(x_j-z)}{\tau_{p_*}(x_j)}.$$</div>
<p>For each shape, every other edge carries $\tau_{p_*,r}$, which vanishes when the lattice distance between its endpoints exceeds $r$. There are $2k$ such edges connecting all remaining positions to zero. Hence every contributing position, including $z$, lies in the deterministic ball of radius $2kr$. The resulting diagram sum is finite. The ratio hypothesis therefore permits passage to the limit term by term, after which successive leaf sums give $s_{p_*}(r)^{2k}$. Cylinder convergence of $|B(r)|^k$ proves the second assertion. The case $r=0$ is also covered: every short factor then forces its endpoints to coincide.</p>
<p>The <a href="/tag/E22E/">compactness and escape theorem</a> supplies infinite-root support for both constructions. In particular, locally finite infinite clusters give $|B(r)|\ge r+1$ almost surely. A positive spatial equivalent $\tau_{p_*}(x)\sim A|x|^{2-d}$ supplies the stated ratio hypothesis, since $|x_j-z|/|x_j|\to1$. Neither a general two-sided spatial bound alone nor cylinder convergence alone is substituted for that ratio limit.</p>

## Exponential intrinsic-volume tails under a finite triangle {#section-intrinsic-volume-tail}

<a id="tag-Z78U" data-assertion="theorem" data-title="A finite triangle gives exponential upper tails for intrinsic IIC volume on the radius-squared scale"></a>
<p>Let $d\ge2$ and suppose nearest-neighbour percolation has finite critical triangle $D=\Delta_{p_c}(0)$. Put</p>
<div class="math-display">$$b=-2d\log(1-p_c),\qquad A=eD^2(2+3b).$$</div>
<p>Let $\mu$ be any susceptibility-biased cylinder limit as $p\uparrow p_c$, or any distant-point cylinder limit at $p_c$ satisfying the ratio hypothesis of KIGU. For every integer $r\ge0$ and $0\le t<1/2$,</p>
<div class="math-display">$$\mathbb E_\mu\exp\!\left(\frac{t|B(r)|}{A^2(r+1)^2}\right)
\le(1-2t)^{-1/2}.$$</div>
<p>Consequently, for every $\lambda\ge0$,</p>
<div class="math-display">$$\mu\bigl(|B(r)|\ge\lambda A^2(r+1)^2\bigr)
\le\sqrt2\,e^{-\lambda/4}.$$</div>
<p>There is a deterministic constant $C<\infty$, depending on the model, such that almost surely</p>
<div class="math-display">$$r+1\le|B(r)|\le C r^2\log\log r$$</div>
<p>for all sufficiently large integers $r$. The starting radius may depend on the configuration. In particular,</p>
<div class="math-display">$$\limsup_{r\to\infty}\frac{\log|B(r)|}{\log r}\le2.$$</div>
<p><em>Proof.</em> Use weights $1/(2d)$ and intensity $\beta=-2d\log(1-p)$. For $r\ge1$, take $\alpha=br/(r+1)$. The <a href="/tag/PI11/">short-path thinning comparison</a> and <a href="/tag/ADWR/">the finite-triangle susceptibility bound</a> give</p>
<div class="math-display">$$s_{p_c}(r)\le\left(1+\frac1r\right)^r\chi(\alpha)
\le eD^2(2+3br)\le A(r+1).$$</div>
<p>Here $\chi(\alpha)$ uses the normalized intensity parameter, and $\alpha b/(b-\alpha)=br$. At $r=0$, $s_{p_c}(0)=1\le A$, since $D\ge1$ and $b\ge1$. KIGU now bounds the $k$th moment of $|B(r)|/[A^2(r+1)^2]$ by $(2k-1)!!$. Including $k=0$ with $(-1)!!=1$, Tonelli and the binomial series yield</p>
<div class="math-display">$$\mathbb E_\mu e^{t|B(r)|/[A^2(r+1)^2]}
\le\sum_{k\ge0}\frac{(2k-1)!!}{k!}t^k=(1-2t)^{-1/2}.$$</div>
<p>Take $t=1/4$ and apply Markov's inequality for the tail estimate. At dyadic radii $r=2^j$, $j\ge2$, choose $\lambda=12\log j$. The exceptional probabilities are at most $\sqrt2j^{-3}$, hence summable. Borel–Cantelli gives the upper bound along these radii, and monotonicity of the intrinsic balls extends it to every sufficiently large radius, with another fixed constant. Infinite-root support gives the lower bound $r+1$. Dividing logarithms proves the last assertion.</p>
<p>This is an upper volume estimate. It supplies neither a matching radius-squared lower bound nor a spectral-dimension theorem. It also does not prove full-sequence IIC convergence, equality of constructions or one-endedness. The spatial equivalent in <a href="/tag/FWHO/">the Gaussian asymptotic theorem</a> supplies KIGU's ratio input in the regimes where that theorem's hypotheses have been verified.</p>


## Stopping at an intrinsic boundary {#section-boundary-density}

<p>The remaining intrinsic-volume estimate comes from stopping at a small boundary. This is the argument behind Kozma–Nachmias, Lemma 2.3. For susceptibility bias, expected unexplored cluster mass takes the place of connection probability to a distant point. We first state the exploration comparison that permits this change of conditioning.</p>
<p>On the nearest-neighbour lattice write $S(j)=B(j)\setminus B(j-1)$, with $B(-1)=\varnothing$. The history $\mathcal H_j$ records the exploration obtained by revealing all bonds with at least one endpoint in $B(j-1)$; $\mathcal H_0$ is trivial. In particular it determines $B(j)$ and $S(j)$, but does not reveal bonds between vertices of $S(j)$ or beyond that sphere. Each bounded-depth history depends on a deterministic finite set of bonds. Conditional on a possible history, the unrevealed bonds retain their independent Bernoulli law.</p>

<a id="tag-KGPE" data-assertion="theorem" data-title="A stopped intrinsic boundary bounds the density of an incipient cylinder limit"></a>
<p>Let $J$ be a stopping time for $(\mathcal H_j)$ with values in $\{1,\ldots,R\}$, where $R<\infty$, and let $F\ge0$ be a bounded $\mathcal H_J$-measurable function. If $p_n\to p_*$, $\chi(p_n)<\infty$, $\chi(p_n)\to\infty$ and $Q_{p_n}$ converges on cylinders to $\mu$, then</p>
<div class="math-display">$$\mathbb E_\mu F\le\mathbb E_{p_*}\bigl[F|S(J)|\bigr].$$</div>
<p>For a cylinder limit $\nu$ of $\mathbb P_{p_*}(\,\cdot\mid0\leftrightarrow x_n)$, with $|x_n|\to\infty$ and $\tau_{p_*}(x_n)>0$, the corresponding bound is</p>
<div class="math-display">$$\mathbb E_\nu F\le L\mathbb E_{p_*}\bigl[F|S(J)|\bigr],$$</div>
<p>provided $L<\infty$ and $\limsup_n\tau_{p_*}(x_n-z)/\tau_{p_*}(x_n)\le L$ for every fixed $z$. In particular KIGU's ratio hypothesis gives $L=1$.</p>
<p><em>Proof.</em> Fix an exploration history through level $j$. Every vertex of the root cluster outside $B(j-1)$ can be reached from some $v\in S(j)$ without entering $B(j-1)$: take the part of a root-to-vertex path after its last exit from $B(j-1)$. All bonds of this remaining path are unrevealed. Deleting the explored vertices cannot increase connection probabilities under the independent law, so</p>
<div class="math-display">$$\mathbb E_p\bigl[|C(0)|\mid\mathcal H_j\bigr]
\le |B(j-1)|+|S(j)|\chi(p).$$</div>
<p>On each event $\{J=j\}$ the same inequality applies, since that event and $F$ are determined by the history. Multiplication by $F$, summation over $j$ and division by $\chi(p)$ give</p>
<div class="math-display">$$\mathbb E_{Q_p}F\le
\mathbb E_p\bigl[F|S(J)|\bigr]
+\frac{\mathbb E_p[F|B(J-1)|]}{\chi(p)}.$$</div>
<p>All observables on the right are bounded cylinder functions, with bounds depending only on $R$ and $F$. Their independent-law expectations are continuous in $p$; the last term tends to zero. Cylinder convergence proves the first assertion.</p>
<p>For the second, take $n$ large enough that $x_n$ is outside the deterministic radius-$R$ ball. The same last-exit argument gives, on each stopped history,</p>
<div class="math-display">$$\mathbb P_{p_*}(0\leftrightarrow x_n\mid\mathcal H_J)
\le\sum_{v\in S(J)}\tau_{p_*}(x_n-v).$$</div>
<p>After multiplication by $F$ and normalization by $\tau_{p_*}(x_n)$, only finitely many possible vertices $v$ remain. Taking the upper limit proves the claimed bound. No convergence on an infinite-coordinate connection event is used.</p>
<p>For example, two-sided spatial bounds $c|x|^{2-d}\le\tau_{p_*}(x)\le C|x|^{2-d}$ for all sufficiently large $|x|$ give $L=C/c$. This yields a bounded-density comparison; it does not assert the ratio limit with value one.</p>

## Quadratic intrinsic volume {#section-quadratic-volume}

<p>For the rest of this article let $d\ge2$, assume $D=\Delta_{p_c}(0)<\infty$, and let $\mu$ be either a susceptibility-biased cylinder limit as $p\uparrow p_c$ or a distant-point cylinder limit satisfying KIGU's ratio hypothesis. These are the same laws as in Z78U. Retain $A=eD^2(2+3b)$, where $b=-2d\log(1-p_c)$.</p>
<p>The <a href="/tag/ADWR/">finite-triangle critical tail</a> and <a href="/tag/KEO7/">the uniform intrinsic-arm theorem</a> give a constant $K<\infty$ such that</p>
<div class="math-display">$$\sup_{H,v}\mathbb P_{p_c}^{H}\bigl(S_H(v,n)\ne\varnothing\bigr)\le\frac K n\qquad(n\ge1),$$</div>
<p>where $H$ ranges over deterministic subgraphs of the lattice and $v$ over their vertices. Deleted bonds are fixed closed. Increase $K$ if necessary so that $K\ge1$. Uniformity over $H$ will matter for resistance; the volume proof only needs the full lattice.</p>

<a id="tag-RG3Z" data-assertion="theorem" data-title="Finite triangle gives a quadratic lower-volume tail and intrinsic IIC volume exponent two"></a>
<p>For every integer $r\ge1$ and $0<\varepsilon<1$,</p>
<div class="math-display">$$\mu\bigl(|B(r)|\le\varepsilon r^2\bigr)\le4K\varepsilon.$$</div>
<p>For each fixed $\delta>0$, there are deterministic constants $c_\delta,C>0$ such that, almost surely,</p>
<div class="math-display">$$\frac{c_\delta r^2}{(\log r)^{1+\delta}}
\le |B(r)|\le Cr^2\log\log r$$</div>
<p>for all sufficiently large integers $r$. Consequently</p>
<div class="math-display">$$\lim_{r\to\infty}\frac{\log|B(r)|}{\log r}=2\qquad\mu\text{-almost surely}.$$</div>
<p><em>Proof.</em> The limiting cluster is infinite by E22E, so every intrinsic sphere is nonempty. Suppose $r\ge2$ and put $m=\lceil r/2\rceil$. There are at least $r/2$ levels in $\{m,\ldots,r\}$. If $|B(r)|\le\varepsilon r^2$, one of their spheres has size at most $2\varepsilon r$.</p>
<p>Explore until the first such level with $1\le|S(j)|\le2\varepsilon r$. Stop at $r$ if there is no such level, and write $H$ for the event that a level was found. This defines a bounded stopping time $J$, and $H\in\mathcal H_J$. On $H$, $|S(J)|\le2\varepsilon r$ and $S(m)\ne\varnothing$. KGPE therefore gives</p>
<div class="math-display">$$\mu\bigl(|B(r)|\le\varepsilon r^2\bigr)
\le\mu(H)\le2\varepsilon r\,\mathbb P_{p_c}(H)
\le2\varepsilon r\,\frac K m\le4K\varepsilon.$$</div>
<p>The positive lower bound on the selected sphere is essential: an extinct critical cluster must not contribute to $H$. If $2\varepsilon r<1$, no level can be selected and the small-volume event has zero limiting probability. For $r=1$ that event is also impossible.</p>
<p>At $r=2^j$, take $\varepsilon=j^{-(1+\delta)}$. The resulting exceptional probabilities are summable. Borel–Cantelli gives the lower bound at these radii, and monotonicity of $B(r)$ in $r$ extends it to all large radii, changing the deterministic constant. Z78U supplies the upper bound. Dividing logarithms gives the limit. This comparison uses monotonicity in radius, not monotonicity of an intrinsic sphere event in the bonds.</p>
<p>KGPE also gives the lower-tail estimate $4LK\varepsilon$ for distant-point limits with its weaker finite-$L$ hypothesis. The two-sided almost-sure conclusion above uses Z78U's upper bound under the stated ratio hypothesis. Neither conclusion identifies different IIC constructions or proves full-sequence convergence.</p>

## Transferring an explored event {#section-history-transfer}

<a id="tag-3FTE" data-assertion="theorem" data-title="Intrinsic exploration events transfer from critical percolation to IIC limits with a square-root loss"></a>
<p>Under the hypotheses of RG3Z, for every integer $r\ge1$ and event $E\in\mathcal H_r$,</p>
<div class="math-display">$$\mu(E)\le\min\bigl\{1,\,6A\sqrt{r\mathbb P_{p_c}(E)}\bigr\}.$$</div>
<p><em>Proof.</em> KIGU and the critical ball-mean bound used in Z78U imply</p>
<div class="math-display">$$\sum_{j=r}^{2r}\mathbb E_\mu|S(j)|
\le\mathbb E_\mu|B(2r)|\le A^2(2r+1)^2\le9A^2r^2.$$</div>
<p>Choose a deterministic $j\in\{r,\ldots,2r\}$ with $\mathbb E_\mu|S(j)|\le9A^2r$. For any $M>0$, split according to whether this sphere has more than $M$ vertices. Markov's inequality and KGPE at the fixed stopping time $j$ give</p>
<div class="math-display">$$\mu(E)\le\frac{9A^2r}{M}
+\mathbb E_{p_c}\bigl[\mathbf1_E\mathbf1_{\{|S(j)|\le M\}}|S(j)|\bigr]
\le\frac{9A^2r}{M}+M\mathbb P_{p_c}(E).$$</div>
<p>Here $E\in\mathcal H_j$ because $j\ge r$. If $\mathbb P_{p_c}(E)>0$, take $M=3A\sqrt{r/\mathbb P_{p_c}(E)}$. If it is zero, let $M\to\infty$.</p>

## Resistance through intrinsic layers {#section-intrinsic-resistance}

<p>Give every open bond conductance one. Let $\mathcal R(r)$ be the effective resistance from zero to the wired sphere $S(r)$ in the finite open graph on $B(r)$. Equivalently, it is the infimum of $\sum_e i(e)^2$ over unit flows from zero to that wired sphere, counting each unoriented bond once. Set $\mathcal R(r)=\infty$ if $S(r)$ is empty. Bonds with both endpoints in $S(r)$ disappear after wiring, so $\mathcal R(r)$ is determined by $\mathcal H_r$.</p>

<a id="tag-POD2" data-assertion="theorem" data-title="Finite triangle gives linear intrinsic IIC resistance growth"></a>
<p>Under the hypotheses of RG3Z, there is a constant $C_R<\infty$ such that for all integers $r\ge8$ and $\lambda>1$,</p>
<div class="math-display">$$\mu\bigl(\mathcal R(r)\le r/\lambda\bigr)
\le C_R\lambda^{-1/2}.$$</div>
<p>One may take $C_R=96A\sqrt{dKA}$. For every fixed $\delta>0$, almost surely</p>
<div class="math-display">$$\frac{c_\delta r}{(\log r)^{2+\delta}}\le\mathcal R(r)\le r$$</div>
<p>for all sufficiently large integers $r$, with a deterministic $c_\delta>0$. In particular $\log\mathcal R(r)/\log r\to1$ almost surely.</p>
<p><em>Proof.</em> For $j\in I=\{\lceil r/4\rceil,\ldots,\lfloor r/2\rfloor\}$, let $\Pi_j$ consist of the open bonds from $S(j-1)$ to $S(j)$ that can be followed by an open path to $S(r)$ inside $B(r)$ without returning to $B(j-1)$. Write $L_j=|\Pi_j|$ and $N=\sum_{j\in I}L_j$.</p>
<p>Condition on $\mathcal H_j$, and consider one of the open crossing bonds, with endpoint $v\in S(j)$. If it belongs to $\Pi_j$, then in the graph obtained by removing $B(j-1)$, the vertex $v$ connects to a vertex at root distance $r$. Its distance from $v$ in that graph is at least $r-j$: a shorter path, preceded by a length-$j$ root path, would contradict that root distance. Thus the unexplored graph has a nonempty intrinsic sphere about $v$ at radius $r-j$. Its bonds are still independent, and the uniform subgraph arm bound gives conditional probability at most $K/(r-j)\le2K/r$.</p>
<p>There are at most $2d|S(j)|$ crossing bonds. Since the critical ball mean is at most $A(n+1)$,</p>
<div class="math-display">$$\mathbb E_{p_c}N
\le\frac{4dK}{r}\sum_{j\in I}\mathbb E_{p_c}|S(j)|
\le\frac{4dK}{r}A(\lfloor r/2\rfloor+1)
\le4dKA.$$</div>
<p>When $S(r)$ is nonempty, each $\Pi_j$ separates zero from $S(r)$: the last exit of any root-to-sphere path from $B(j-1)$ uses a bond of $\Pi_j$. These cutsets are pairwise edge-disjoint. For a unit flow, conservation and Cauchy–Schwarz force energy at least $1/L_j$ on the $j$th cutset. Indeed the edge boundary of the root component after deleting $\Pi_j$ is a subset of $\Pi_j$ and carries net current one. Summing these energy bounds and minimizing over flows gives the Nash–Williams inequality in the form</p>
<div class="math-display">$$\mathcal R(r)\ge\sum_{j\in I}\frac1{L_j}
\ge\frac{|I|^2}{N}.$$</div>
<p>For $r\ge8$, $|I|\ge r/8$. Therefore $\mathcal R(r)\le r/\lambda$ implies $N\ge\lambda r/64$. If the outer sphere is empty, the resistance event is false. Markov's inequality now yields the independent-law estimate</p>
<div class="math-display">$$\mathbb P_{p_c}\bigl(\mathcal R(r)\le r/\lambda\bigr)
\le\frac{256dKA}{\lambda r}.$$</div>
<p>Apply 3FTE to this $\mathcal H_r$-measurable event to obtain the asserted constant $C_R$.</p>
<p>Under $\mu$ the root cluster is infinite. A shortest open path to $S(r)$ carries a unit flow of energy $r$, giving $\mathcal R(r)\le r$. Also $\mathcal R(r)$ is nondecreasing in $r$: restricting a unit flow to a smaller ball and wiring its boundary cannot increase its energy. At $r=2^j$, take $\lambda=j^{2+\delta}$. The preceding exceptional probabilities are summable, so Borel–Cantelli and this radius monotonicity give the eventual lower bound. Taking logarithms proves the resistance exponent.</p>
<p>These are volume and resistance conclusions for each admissible cylinder limit. Kozma–Nachmias use an additional random-walk theorem to obtain the Alexander–Orbach conclusions. That theorem is not proved or invoked here; spectral dimension, heat-kernel estimates and walk displacement remain separate work. The argument above uses the finite-triangle critical tail, short-path thinning and uniform subgraph arms, and does not use the reverse-BK argument assigned to FIXER.</p>

<p>The <a href="/articles/iic-random-walk/">random-walk article</a> now proves the Green-function and return-kernel implications needed for the conclusions left separate above. Under the same finite-triangle hypotheses, <a href="/tag/IXCJ/">IXCJ</a> gives recurrence, quenched mean intrinsic exit-time exponent three and spectral dimension four thirds for each admissible cylinder limit. Sample-path displacement, range and identification of constructions remain separate.</p>

<p>The <a href="/tag/HJKG/">pathwise random-walk theorem</a> now complements the mean-exit and spectral-dimension conclusions: on almost every admissible limiting cluster, exit times have exponent three, maximum intrinsic distance has exponent one third, and the number of visited vertices has exponent two thirds almost surely under the walk law. Instantaneous displacement has its exponent only in probability; recurrence precludes the corresponding almost-sure limit.</p>

<p>The <a href="/tag/G85Z/">annealed walk bounds</a> now give two-sided mean exit times of order $r^3$ and averaged even-time return probabilities of order $n^{-2/3}$ for the same incipient limits. The proof controls rare environments using the lower-volume tail and gives a lower bound of order $n^{1/3}$ on mean intrinsic displacement; it does not infer expectations from almost-sure logarithmic exponents.</p>

<p>The <a href="/tag/YWT9/">quantitative walk estimates</a> give tightness of intrinsic displacement and maximum distance on the $n^{1/3}$ scale, and exit time on the $r^3$ scale, under the joint cluster-and-walk law. Explicit polynomial tails also give positive and negative fractional moments in the stated ranges; they do not supply the missing upper mean-displacement bound.</p>

<p>The <a href="/tag/PSNV/">quantitative range theorem</a> now gives tightness of the number of visited vertices on the $n^{2/3}$ scale, with inverse and positive fractional moments for $-3/23&lt;p&lt;3/94$. The proof combines a bound on the volume missed before exit with the exponential intrinsic-volume tail. It distinguishes these joint-law bounds from the earlier almost-sure logarithmic exponent.</p>


<p>The <a href="/tag/9JIV/">quadratic small-displacement bound</a> now uses the available second volume moment to sharpen the earlier linear estimate. Its matching lower bound, including odd times for ordinary walk, yields the <a href="/tag/FPDW/">inverse-position moment transition</a>: orders below two scale with displacement, order two has a logarithmic factor, and orders above two are governed by returns to a fixed neighbourhood. These conclusions hold for both incipient limits under their existing hypotheses.</p>


<p>The <a href="/tag/ZZC8/">root local-time theorem</a> gives visit-count moments of order $(n+1)^{p/3}$ for $-3/4&lt;p&lt;3$, an almost-sure visit-count exponent of one third, and exponent three for successive root return times. Its <a href="/tag/7UZM/">finite-time occupation bound</a> uses resistance and an upper volume bound; it does not require an inverse-volume moment. The count includes every visit to the root, rather than distinct vertices in the range.</p>


<p>The <a href="/tag/KMWL/">cubic occupation-tail bound</a> supplies explicit, possibly nonsharp bounds at the root visit-count moment endpoints. Inverting the visit count gives <a href="/tag/2XZU/">successive return-time moments</a> of order $m^{3p}$ for $-1&lt;p&lt;1/4$, together with quantitative upper and lower tails on the scale $m^3$.</p>


<p>For susceptibility-biased cylinder limits, <a href="/tag/K11N/">weighting by the root degree</a> makes the environment seen from the walk stationary and preserves marked paths under time reversal. This yields <a href="/tag/BP8X/">a cubic small-range tail</a>, inverse range moments through every order below three, and a mean-range upper bound of order $(n+1)^{3/4}(\log(e(n+1)))^{1/4}$. This argument is specific to susceptibility bias; it does not identify a distant-point limit with that construction.</p>
