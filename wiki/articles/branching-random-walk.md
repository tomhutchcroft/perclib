---
{
  "id": "branching-random-walk",
  "title": "Branching random walk and Green diagrams",
  "subtitle": "Occupation identities and diagrams for finite-range and power-law walks",
  "kind": "model",
  "category": "Models",
  "summary": "Critical branching random walk has random-walk Green function as its expected occupation density. Fourier inversion gives diagram thresholds for nearest-neighbour and power-law steps, including the logarithmic boundary at tail exponent two.",
  "context": ["Independent offspring variables have finite mean $m$; children move independently according to a Markov kernel.", "Occupation counts retain multiplicity: different particles and different generations can visit the same site.", "The first Fourier calculation is for lazy nearest-neighbour walk on $\\mathbb Z^d$, $d\\geq1$."],
  "related": ["branching-processes", "exploration", "triangle-condition", "susceptibility"],
  "sourceIds": ["hutchcroft-book", "perclib-train10-models-longrange-fouriersymbol"],
  "aliases": ["branching random walk", "Green function", "bubble diagram", "triangle diagram", "upper critical dimension", "occupation density"],
  "prototypeUses": []
}
---

## The branching walk {#section-model}

<a id="tag-CYYG" data-assertion="definition" data-title="Branching random walk and its occupation counts"></a><p>Let $S$ be a countable state space and $P$ a Markov transition kernel on $S$. Begin with one particle at $x$. Each particle has an independent copy of a nonnegative integer-valued offspring variable $\xi$, with $m=\mathbb E\xi&lt;\infty$. Conditional on the parent's location $z$, each child independently moves according to $P(z,\cdot)$; these moves are independent of all offspring variables. Write $N_n(y)$ for the number of generation-$n$ particles at $y$, and</p><div class="math-display">$$L_y=\sum_{n\geq0}N_n(y)\in\mathbb N\cup\{\infty\}$$</div><p>for its total occupation count. The total population in generation $n$ is the <a href="/tag/NCWZ/">Galton–Watson generation size</a>. Criticality here means $m=1$; it refers to the branching mechanism.</p>

<a id="tag-94E7" data-assertion="proposition" data-title="First moments of branching-random-walk occupation"></a><p>For every $n\geq0$ and $y\in S$,</p><div class="math-display">$$\mathbb E_x N_n(y)=m^nP^n(x,y),\qquad \mathbb E_x L_y=\sum_{n\geq0}m^nP^n(x,y).$$</div><p>Here $P^0(x,y)=\mathbf1_{\{x=y\}}$ and $m^0=1$, including when $m=0$. At criticality, the expected occupation is exactly the Markov-chain Green function</p><div class="math-display">$$G(x,y)=\sum_{n\geq0}P^n(x,y).$$</div><p><em>Proof.</em> Conditional on generation $n$ and its locations, each particle at $z$ contributes an expected $mP(z,y)$ children at $y$. Taking expectations gives</p><div class="math-display">$$\mathbb E_xN_{n+1}(y)=m\sum_z\mathbb E_xN_n(z)P(z,y).$$</div><p>Induction and the Markov-kernel composition rule prove the first formula. Tonelli gives the occupation formula. When $m=0$, there are no children almost surely, so only generation zero contributes.</p><p>This is an expectation, not a hitting probability. The event that the branching walk ever visits $y$ has probability $\mathbb P_x(L_y&gt;0)\leq\min\{1,\mathbb E_xL_y\}$, and equality need not hold. A particle system can visit a site many times. Even at a nondegenerate critical offspring law, where the family tree is finite almost surely, expected occupation may be infinite on a recurrent underlying walk.</p>

## Independent collision counts {#section-collisions}

<a id="tag-4F49" data-assertion="proposition" data-title="Expected collision multiplicity of independent critical branching walks"></a><p>Let $L$ and $\widetilde L$ be the occupation fields of two independent critical branching random walks started at $x$ and $z$, using the same kernel $P$. If $G(x,y)$ and $G(z,y)$ are finite for each $y$, then the total number of pairs of visits to a common site, counted with multiplicity, satisfies</p><div class="math-display">$$\mathbb E\sum_yL_y\widetilde L_y=\sum_yG(x,y)G(z,y).$$</div><p>Either side may be infinite. In particular, for a symmetric translation-invariant kernel on $\mathbb Z^d$ and two walks started at zero, the right side is the bubble diagram $\sum_yG(0,y)^2$.</p><p><em>Proof.</em> Independence gives $\mathbb E[L_y\widetilde L_y]=\mathbb E L_y\,\mathbb E\widetilde L_y$; this follows first for bounded truncations and then by monotone convergence. Sum over $y$ using Tonelli and apply the occupation identity.</p><p>This counts pairs of particles or generations visiting a site, not the cardinality of the intersection of their ranges. A divergent expected count does not by itself imply an infinite count almost surely, or determine the probability that the ranges intersect. Such distinctions matter when using a diagram as a geometric heuristic.</p>

## Two visits in the same family tree {#section-pair-occupation}

<a id="tag-J1E9" data-assertion="proposition" data-title="Second occupation moment of a critical branching random walk"></a>
<p>Suppose the offspring mean is one and its variance is $\sigma^2&lt;\infty$, allowing $\sigma^2=0$. Assume $G(u,v)&lt;\infty$ for every pair of states, and write</p>
<div class="math-display">$$H(u,v)=\sum_{n\geq1}P^n(u,v)=\sum_wP(u,w)G(w,v).$$</div>
<p>For a single branching random walk started at $x$,</p>
<div class="math-display">$$\begin{aligned}
\mathbb E_x[L_yL_z]={}&\mathbf1_{\{y=z\}}G(x,y)+G(x,y)H(y,z)+G(x,z)H(z,y)\\
&+\sigma^2\sum_wG(x,w)H(w,y)H(w,z).
\end{aligned}$$</div>
<p>The equality is an equality of nonnegative extended quantities. In particular, finiteness of all first occupation moments does not require the sum on the second line to be finite. When $\sigma^2=0$, that line is defined to be zero.</p>
<p><em>Proof.</em> Expand $L_yL_z$ as the number of ordered pairs of particles whose locations are $y$ and $z$. Classify a pair by its genealogy. If both entries are the same particle, their expected number is $\mathbf1_{\{y=z\}}G(x,y)$.</p>
<p>If the first particle is a strict ancestor of the second, a particle at $y$ has an expected $H(y,z)$ strict descendants at $z$, by the first-moment identity summed over positive generations. Its future reproduction and displacements have the original laws, independently of the information that placed it at $y$. Summing over particles at $y$ gives $G(x,y)H(y,z)$. Reversing the ancestral relation gives $G(x,z)H(z,y)$.</p>
<p>Otherwise the pair has a unique most recent common ancestor, and the two particles lie in the subtrees of distinct children of that ancestor. Conditional on an ancestor at $w$ having $k$ children, there are $k(k-1)$ ordered choices of these children. For each chosen child, the expected total occupation at $y$, including that child itself after its first step, is $\sum_vP(w,v)G(v,y)=H(w,y)$. The two child subtrees and their first steps are independent. Averaging over $k$ therefore gives $\mathbb E[\xi(\xi-1)]H(w,y)H(w,z)=\sigma^2H(w,y)H(w,z)$ per ancestor at $w$. Summing over ancestors gives the second line.</p>
<p>All these decompositions count nonnegative terms, so Tonelli justifies the sums even when the second moment is infinite. They apply also to the deterministic one-child law: the family is then a single infinite walk, there are no distinct child subtrees, and only the first three terms remain.</p>
<p>The two factors of $H$ in the branching term start with separate child steps. Replacing them by $G$ would count visits at the common ancestor again, although those belong to the first three terms. Likewise, the product of first moments for two independent branching walks cannot replace this same-tree identity. Neither identity identifies a visit count with a hitting probability or with the percolation two-point function.</p>

## A precise Fourier calculation {#section-diagrams}

<p>Now let $P$ be lazy nearest-neighbour walk on $\mathbb Z^d$: a step stays put with probability $1/2$ and takes each of the $2d$ coordinate steps with probability $1/(4d)$. Write $G(u)=G(0,u)$ and define nonnegative extended sums</p><div class="math-display">$$B=\sum_uG(u)^2,\qquad T=\sum_{u,v}G(u)G(v-u)G(v).$$</div>

<a id="tag-E9BP" data-assertion="theorem" data-title="Green, bubble and triangle thresholds for lazy nearest-neighbour walk"></a><p>For this walk,</p><div class="math-display">$$G(0)&lt;\infty\ \Longleftrightarrow\ d&gt;2,\qquad B&lt;\infty\ \Longleftrightarrow\ d&gt;4,\qquad T&lt;\infty\ \Longleftrightarrow\ d&gt;6.$$</div><p><em>Proof.</em> Introduce $G_r(u)=\sum_{n\geq0}r^nP^n(0,u)$ for $0\leq r&lt;1$. It lies in $\ell^1(\mathbb Z^d)$, with total mass $(1-r)^{-1}$. The one-step Fourier transform on $[-\pi,\pi]^d$ is</p><div class="math-display">$$\varphi(k)=\frac12+\frac1{2d}\sum_{j=1}^d\cos k_j,\qquad \widehat G_r(k)=\frac1{1-r\varphi(k)}.$$</div><p>Absolute summability justifies multiplying transforms and inverting convolutions. Symmetry therefore gives, for $j=1,2,3$,</p><div class="math-display">$$(G_r^{*j})(0)=\frac1{(2\pi)^d}\int_{[-\pi,\pi]^d}\frac{dk}{(1-r\varphi(k))^j}.$$</div><p>The cases $j=1,2,3$ on the left are respectively $G_r(0)$, $\sum_uG_r(u)^2$ and $\sum_{u,v}G_r(u)G_r(v-u)G_r(v)$. As $r\uparrow1$, all their summands increase to the corresponding undamped values. Also $0\leq\varphi\leq1$, so the integrands increase. Monotone convergence on both sides yields the same identity with $r=1$, allowing infinite values.</p><p>The only point of the torus where $\varphi=1$ is zero. Moreover,</p><div class="math-display">$$1-\varphi(k)=\frac1{2d}\sum_{j=1}^d(1-\cos k_j)\asymp |k|^2\quad\text{near zero}.$$</div><p>Away from zero the denominator is bounded below. Thus the integral for convolution order $j$ is finite exactly when $\int_0^\varepsilon \rho^{d-1-2j}\,d\rho$ is finite, which is equivalent to $d&gt;2j$. This proves all three thresholds. At $d=2j$, the spatial-frequency integral with a small ball of radius $a$ removed diverges on the order of $\log(1/a)$ as $a\downarrow0$.</p>

## Long-range step distributions {#section-long-range-symbol}

<a id="tag-VJCW" data-assertion="theorem" data-title="Fourier symbol of a power-law lattice step distribution"></a>
<p>Let $p$ be a symmetric probability mass function on $\mathbb Z^d$, $d\geq1$, with $p(0)\geq1/2$. Suppose that for some $\alpha&gt;0$ and constants $0&lt;c\leq C&lt;\infty$,</p>
<div class="math-display">$$c|x|^{-d-\alpha}\leq p(x)\leq C|x|^{-d-\alpha}\qquad(x\ne0),$$</div>
<p>where $|\cdot|$ is the Euclidean norm. Write $\varphi(k)=\sum_xp(x)\cos(k\cdot x)$ for $k\in[-\pi,\pi]^d$. Then $0\leq\varphi\leq1$, and $\varphi(k)=1$ only at the origin of the torus. Uniformly as $|k|\downarrow0$,</p>
<div class="math-display">$$1-\varphi(k)\asymp
\begin{cases}
|k|^\alpha,&0&lt;\alpha&lt;2,\\
|k|^2\log(1/|k|),&\alpha=2,\\
|k|^2,&\alpha&gt;2.
\end{cases}$$</div>
<p><em>Proof.</em> Laziness gives $\varphi(k)\geq p(0)-(1-p(0))\geq0$. Every coordinate unit vector has positive mass, so $\sum_xp(x)(1-\cos(k\cdot x))$ vanishes only when every coordinate of $k$ is zero modulo $2\pi$. Continuity then bounds $1-\varphi$ away from zero outside any neighbourhood of that point.</p>
<p>Put $\rho=|k|$ and take $R=\rho^{-1}\geq2$. The inequalities $1-\cos u\leq\min\{u^2/2,2\}$ give</p>
<div class="math-display">$$1-\varphi(k)\leq C'\left[\rho^2\sum_{0&lt;|x|\leq R}|x|^{2-d-\alpha}
+\sum_{|x|&gt;R}|x|^{-d-\alpha}\right].$$</div>
<p>For the lower bound, retain only $|x|\leq R$, where $|k\cdot x|\leq1$ and $1-\cos(k\cdot x)\geq c'(k\cdot x)^2$. Sign changes cancel the mixed coordinate sums in the radial reference weight, and coordinate permutations make the diagonal sums equal. Hence</p>
<div class="math-display">$$1-\varphi(k)\geq c''\sum_{0&lt;|x|\leq R}|x|^{-d-\alpha}(k\cdot x)^2
=\frac{c''\rho^2}{d}\sum_{0&lt;|x|\leq R}|x|^{2-d-\alpha}.$$</div>
<p>Lattice shells give $\sum_{|x|&gt;R}|x|^{-d-\alpha}\asymp R^{-\alpha}$. The truncated sum is comparable to $R^{2-\alpha}$ for $\alpha&lt;2$, to $\log R$ for $\alpha=2$, and to $1$ for $\alpha&gt;2$: a dyadic annulus of radius $s$ contains order $s^d$ lattice points and contributes order $s^{2-\alpha}$. Inserting these estimates proves all three cases. Radial symmetry of $p$ itself is unnecessary; only its two-sided comparison with the radial weight was used.</p>

## Green-function diagram thresholds {#section-long-range-diagrams}

<a id="tag-1POM" data-assertion="theorem" data-title="Long-range Green, bubble and triangle finiteness including the logarithmic boundary"></a>
<p>For the walk with step distribution $p$ in <a href="/tag/VJCW/">VJCW</a>, put $G_r(x)=\sum_{n\geq0}r^np^{*n}(x)$, $0\leq r&lt;1$, and $G(x)=\sum_{n\geq0}p^{*n}(x)$. For each integer $j\geq1$, the extended convolution sum $D_j=(G^{*j})(0)$ satisfies</p>
<div class="math-display">$$D_j=\frac1{(2\pi)^d}\int_{[-\pi,\pi]^d}(1-\varphi(k))^{-j}\,dk.$$</div>
<p>Its finiteness criterion is</p>
<div class="math-display">$$D_j&lt;\infty\quad\Longleftrightarrow\quad
\begin{cases}
d&gt;j\alpha,&0&lt;\alpha&lt;2,\\
d&gt;2j\ \text{or}\ (d=2j\ \text{and}\ j&gt;1),&\alpha=2,\\
d&gt;2j,&\alpha&gt;2.
\end{cases}$$</div>
<p>Here $D_1=G(0)$, $D_2=\sum_xG(x)^2$ is the bubble, and $D_3=\sum_{x,y}G(x)G(y-x)G(y)$ is the triangle. In particular, at $\alpha=2$ the bubble is finite in dimension four and the triangle is finite in dimension six.</p>
<p><em>Proof.</em> For $r&lt;1$, $G_r\in\ell^1$ with sum $(1-r)^{-1}$ and Fourier transform $(1-r\varphi)^{-1}$. Multiplication of transforms and Fourier inversion give</p>
<div class="math-display">$$(G_r^{*j})(0)=\frac1{(2\pi)^d}\int_{[-\pi,\pi]^d}(1-r\varphi(k))^{-j}\,dk.$$</div>
<p>Every summand on the left increases as $r\uparrow1$. The integrands also increase because $\varphi\geq0$. Monotone convergence proves the extended identity without first assuming that $G$ or its diagrams are finite. Symmetry identifies the bubble and triangle sums.</p>
<p>Only a neighbourhood of zero can contribute a divergence. For $\alpha\ne2$, <a href="/tag/VJCW/">the symbol estimate</a> reduces integrability to that of $\int_0^\delta \rho^{d-1-jb}\,d\rho$, where $b=\min\{\alpha,2\}$. For $\alpha=2$ the corresponding integral is</p>
<div class="math-display">$$\int_0^\delta\rho^{d-1-2j}\bigl(\log(1/\rho)\bigr)^{-j}\,d\rho.$$</div>
<p>It converges for $d&gt;2j$ and diverges for $d&lt;2j$. At equality the substitution $u=\log(1/\rho)$ gives $\int_{\log(1/\delta)}^\infty u^{-j}\,du$, which is finite exactly when $j&gt;1$. This proves the criterion.</p>

## Discounted divergence orders {#section-discounted-diagrams}

<a id="tag-KEPD" data-assertion="proposition" data-title="Divergence orders of discounted long-range Green diagrams"></a>
<p>Under the same assumptions, let $D_j(r)=(G_r^{*j})(0)$ and $\varepsilon=1-r\downarrow0$. For $\alpha\ne2$ and $b=\min\{\alpha,2\}$,</p>
<div class="math-display">$$D_j(1-\varepsilon)\asymp
\begin{cases}
\varepsilon^{d/b-j},&d&lt;jb,\\
\log(1/\varepsilon),&d=jb,\\
1,&d&gt;jb.
\end{cases}$$</div>
<p>For $\alpha=2$, the orders are instead</p>
<div class="math-display">$$D_j(1-\varepsilon)\asymp
\begin{cases}
\varepsilon^{d/2-j}\bigl(\log(1/\varepsilon)\bigr)^{-d/2},&d&lt;2j,\\
\log\log(1/\varepsilon),&d=2,\ j=1,\\
1,&d&gt;2j\ \text{or}\ (d=2j,\ j&gt;1).
\end{cases}$$</div>
<p>The constants may depend on the fixed step law, $d$ and $j$, but not on $\varepsilon$. In each finite case, $D_j(r)\uparrow D_j&lt;\infty$.</p>
<p><em>Proof.</em> For $r\geq1/2$, $1-r\varphi=\varepsilon+r(1-\varphi)$ is comparable to $\varepsilon+(1-\varphi)$. The integral away from zero remains bounded, and $D_j(r)\geq1$ because every convolution factor has its generation-zero mass at the origin. For $\alpha\ne2$, split the radial integral at $\rho=\varepsilon^{1/b}$. The inner part has order $\varepsilon^{-j}\varepsilon^{d/b}$, and the outer part is comparable to $\int_{\varepsilon^{1/b}}^\delta \rho^{d-1-jb}\,d\rho$. The three cases follow.</p>
<p>For $\alpha=2$, take a fixed $\delta&lt;e^{-1}$ and define $\rho_\varepsilon\in(0,\delta)$ by $\rho_\varepsilon^2\log(1/\rho_\varepsilon)=\varepsilon$. This solution is unique for small $\varepsilon$, and</p>
<div class="math-display">$$\rho_\varepsilon\asymp\sqrt{\frac{\varepsilon}{\log(1/\varepsilon)}}.$$</div>
<p>The inner part has order $\varepsilon^{-j}\rho_\varepsilon^d$. When $d&lt;2j$, the outer integral has order $\rho_\varepsilon^{d-2j}(\log(1/\rho_\varepsilon))^{-j}$, the same quantity. This last integral comparison follows, for example, by differentiating $\rho^{d-2j}(\log(1/\rho))^{-j}$ near zero. At $d=2j$ it is $\int_{\rho_\varepsilon}^\delta d\rho/[\rho(\log(1/\rho))^j]$, giving $\log\log(1/\varepsilon)$ for $j=1$ and a bounded limit for $j&gt;1$. The finite cases also follow from <a href="/tag/1POM/">the undamped criterion</a> and monotone convergence.</p>

## What transfers to percolation {#section-diagram-transfer}

<a id="tag-T79N" data-assertion="proposition" data-title="Pointwise Green domination transfers finite diagram bounds"></a>
<p>Let a translation-invariant independent bond model on $\mathbb Z^d$ have two-point function $t(x)=\mathbb P(0\leftrightarrow x)$. Suppose the Green function above is finite and, for some $A&lt;\infty$,</p>
<div class="math-display">$$t(x)\leq A G(x)\qquad(x\in\mathbb Z^d),$$</div>
<p>including $x=0$. Then, for every integer $j\geq1$,</p>
<div class="math-display">$$(t^{*j})(0)\leq A^jD_j.$$</div>
<p>Thus every finite walk diagram listed in <a href="/tag/1POM/">1POM</a> gives a finite percolation diagram under this domination hypothesis. If also $t(x)\geq aG(x)$ for every $x$, for some $a&gt;0$, the same diagrams are finite or infinite together.</p>
<p><em>Proof.</em> Compare each product of $j$ factors in the nonnegative convolution sum, then sum. Translation invariance and the symmetry of connectivity identify the cases $j=2,3$ with the percolation bubble and triangle. The lower comparison follows in the same way.</p>
<p>The domination estimate is a separate model-specific input. A divergent walk diagram gives no conclusion from an upper bound alone. Nor does finite $D_3$ prove this input or any percolation critical exponent.</p>
<p>The step-law assumption is also essential in the Gaussian Green-function heuristic. For a symmetric lazy law with $p(x)\asymp|x|^{-4}$ on $\mathbb Z^3$ (so $\alpha=1$), <a href="/tag/1POM/">1POM</a> makes the bubble finite. Such a law exists by assigning half the mass to zero and distributing the rest proportionally to $|x|^{-4}$. It cannot satisfy $G(x)\asymp|x|^{-1}$: the lower bound would make $\sum_xG(x)^2$ diverge. The $\alpha=2$ logarithms above describe this specified walk family, not the logarithmic corrections of finite-range critical percolation.</p>

## What the diagram says about percolation {#section-interpretation}

<p>Branching random walk motivates the percolation triangle diagram by replacing the two-point function with a random-walk Green function. The calculation above makes the resulting threshold six exact for the specified walk. It does not prove that the percolation two-point function has that form, or that a particular percolation model satisfies the triangle condition.</p><p>Likewise, the familiar spatial estimate $G(0,x)\asymp |x|^{2-d}$ needs assumptions on the walk and a separate Green-function estimate; an arbitrary step distribution need not have this decay. No such spatial estimate is needed for the Fourier proof above. Long-range steps can change the small-frequency power, and hence the dimensional thresholds.</p><p>The bubble calculation gives a threshold four for the expected collision multiplicity. It cannot be substituted for the triangle diagram governing the mean-field percolation argument. A path-and-cloud dimension count and the prediction of logarithmic percolation corrections at dimension six remain heuristic here. The logarithmic divergence proved above concerns the Green-function integral, not percolation observables.</p>


## The source proof of the three symbol regimes {#section-symbol-source}

<p>The <a href="/coverage/sources/perclib-dfbc5b4-fourier-russo/">Fourier-symbol source</a> proves all three small-frequency comparisons in <a href="/tag/VJCW/">VJCW</a>. Its hypotheses are nonnegative masses of total one and two-sided bounds $c|x|^{-d-\alpha}\leq p(x)\leq C|x|^{-d-\alpha}$ off the origin, with $c&gt;0$, $d\geq1$ and $\alpha&gt;0$. Here $|x|$ is Euclidean. The source uses the cosine series, so without symmetry of $p$ it describes the real part of the complex transform. Symmetry is retained in the walk applications above.</p>
<p>The lower estimate does not reflect $p$. It first replaces $p(x)$ by the radial lower weight $c|x|^{-d-\alpha}$. This weight is invariant under changing the sign of one coordinate. Choose $j$ with $|k_j|\geq|k|/\sqrt d$ and pair that reflection in the deficit sum. The inequality</p>
<div class="math-display">$$(1-\cos(a+b))+(1-\cos(a-b))\geq2(1-|\cos b|)$$</div>
<p>removes the other coordinates. On the face $x_j=n$, $|x_i|\leq n$, there are at least $n^{d-1}$ points, each with Euclidean norm at most $\sqrt d\,n$. Restricting to $n\leq\lfloor1/|k_j|\rfloor$ therefore gives a lower bound proportional to</p>
<div class="math-display">$$k_j^2\sum_{n=1}^{\lfloor1/|k_j|\rfloor}n^{1-\alpha}.$$</div>
<p>For the upper bound, Cauchy–Schwarz and $1-\cos u\leq2\min\{u^2,1\}$ reduce shell counting to $\sum_{n\geq1}n^{-1-\alpha}\min\{s^2n^2,1\}$, where $s=\sqrt d\,|k|$. Split at $1/s$. The partial power sum has order $N^{2-\alpha}$ for $\alpha&lt;2$, order $\log N$ for $\alpha=2$, and stays bounded for $\alpha&gt;2$. The lower bound in the last case already follows from its first term. This yields the three stated orders, including the logarithm at two.</p>
<p>Laziness is needed for $\varphi\geq0$, through $\varphi\geq2p(0)-1$, but not for these deficit estimates. Positivity at coordinate unit vectors makes zero the only frequency in $[-\pi,\pi]^d$ with $\varphi=1$. The source comparisons are up to constants; the Green integrals and their transfer to percolation require the additional arguments above.</p>



## Spatial decay for finite-range walks {#section-finite-range-green}

<a id="tag-02EB" data-assertion="theorem" data-title="An irreducible symmetric finite-range walk has the covariance Green asymptotic"></a>
<p>Let $d\geq3$, and let $p$ be a symmetric probability mass function of finite support on $\mathbb Z^d$. Assume that its support generates $\mathbb Z^d$ as an additive group. Set</p>
<div class="math-display">$$\Sigma=\sum_z p(z)zz^{\mathsf T},\qquad
G_p(x)=\sum_{n=0}^{\infty}p^{*n}(x).$$</div>
<p>Then $\Sigma$ is positive definite, $G_p(x)&lt;\infty$ for every $x$, and, as $\|x\|_2\to\infty$,</p>
<div class="math-display">$$G_p(x)\sim
\frac{\Gamma(d/2-1)}{2\pi^{d/2}\sqrt{\det\Sigma}}
\bigl(x^{\mathsf T}\Sigma^{-1}x\bigr)^{1-d/2}.$$</div>
<p>The equivalent holds along arbitrary lattice directions. No aperiodicity assumption is needed. In particular $G_p(x)\asymp\|x\|_2^{2-d}$ outside a fixed ball.</p>
<p><em>Proof.</em> Symmetry gives mean zero. If $v^{\mathsf T}\Sigma v=0$, then $v\cdot z=0$ for every supported step; the generating assumption forces $v=0$.</p>
<p>We can first make the walk lazy. For $q=(\delta_0+p)/2$, the binomial expansion and Tonelli give</p>
<div class="math-display">$$G_q(x)=\sum_{k\geq0}p^{*k}(x)
\sum_{n\geq k}\binom nk2^{-n}=2G_p(x),\qquad \Sigma_q=\Sigma/2.$$</div>
<p>The inner sum equals two. The proposed expression for $q$ is twice that for $p$, so it suffices to prove the theorem when $p(0)&gt;0$. We make this assumption for the rest of the argument.</p>
<p>We need a bound uniform in both space and time. Put $M(\lambda)=\sum_zp(z)e^{\lambda\cdot z}$ and tilt the step law to</p>
<div class="math-display">$$p_\lambda(z)=\frac{p(z)e^{\lambda\cdot z}}{M(\lambda)}.$$</div>
<p>For $\lambda$ in a fixed small closed ball, these laws have the same finite support and a uniformly positive covariance matrix. Their characteristic functions have modulus one only at zero on the frequency torus: equality forces all supported phases to agree, and the atom at zero and generating assumption force every coordinate phase to be one. Compactness gives a uniform strict bound away from zero. Near zero the squared modulus has expansion $1-\theta^{\mathsf T}\operatorname{Cov}_{p_\lambda}(Z)\theta+O(\|\theta\|_2^3)$, uniformly in $\lambda$. Fourier inversion therefore gives</p>
<div class="math-display">$$p_\lambda^{*n}(x)\leq
(2\pi)^{-d}\int_{[-\pi,\pi]^d}|\widehat p_\lambda(\theta)|^n\,d\theta
\leq Cn^{-d/2}\qquad(n\geq1),$$</div>
<p>uniformly in $x$ and in those tilts. The Gaussian bound near zero controls the integral there, and the strict bound elsewhere contributes an exponentially small term.</p>
<p>Since $p$ is centered and finitely supported, $\log M(\lambda)\leq C_0\|\lambda\|_2^2$ near zero. Let $L$ bound the step length. If $p^{*n}(x)&gt;0$, then $\|x\|_2\leq Ln$. Taking $\lambda=\varepsilon x/n$ with fixed sufficiently small $\varepsilon&gt;0$ in</p>
<div class="math-display">$$p^{*n}(x)=e^{-\lambda\cdot x}M(\lambda)^n p_\lambda^{*n}(x)$$</div>
<p>gives</p>
<div class="math-display">$$p^{*n}(x)\leq Cn^{-d/2}\exp\!\left(-c\frac{\|x\|_2^2}{n}\right)
\qquad(n\geq1, x\in\mathbb Z^d).$$</div>
<p>Outside the reachable ball the left side is zero. Summing the bound without its exponential factor already proves transience for $d&gt;2$.</p>
<p>The same Fourier estimates give the central local limit with its constant. Write</p>
<div class="math-display">$$g_\Sigma(u)=\frac{\exp(-u^{\mathsf T}\Sigma^{-1}u/2)}{(2\pi)^{d/2}\sqrt{\det\Sigma}}.$$</div>
<p>The expansion $\widehat p(\theta)=1-\theta^{\mathsf T}\Sigma\theta/2+O(\|\theta\|_2^3)$ implies convergence of $\widehat p(t/\sqrt n)^n$ to $e^{-t^{\mathsf T}\Sigma t/2}$. On a fixed small frequency neighbourhood the rescaled integrands are dominated by $e^{-c\|t\|_2^2}$; the complement has integral at most $Cn^{d/2}\rho^n$, with $\rho&lt;1$. Thus the rescaled Fourier functions converge in $L^1$. Fourier inversion yields the uniform estimate</p>
<div class="math-display">$$\sup_{x\in\mathbb Z^d}
\left|n^{d/2}p^{*n}(x)-g_\Sigma(x/\sqrt n)\right|\longrightarrow0.$$</div>
<p>Now put $R=\|x\|_2$ and $e=x/R$. For $0&lt;a&lt;b&lt;\infty$, the local limit and a Riemann sum give, uniformly in unit directions $e$,</p>
<div class="math-display">$$R^{d-2}\sum_{aR^2\leq n\leq bR^2}p^{*n}(x)
\longrightarrow\int_a^b t^{-d/2}g_\Sigma(e/\sqrt t)\,dt.$$</div>
<p>The omitted times are uniformly negligible as $a\downarrow0$ and $b\uparrow\infty$. For the early times, the Gaussian bound and dyadic intervals give an upper bound by a constant times</p>
<div class="math-display">$$\sum_{j\geq0}(2^{-j}a)^{1-d/2}\exp(-c2^j/a),$$</div>
<p>which tends to zero with $a$. The late times contribute at most $Cb^{1-d/2}$. Since $x\ne0$, the term $n=0$ is absent. We obtain</p>
<div class="math-display">$$\begin{aligned}
R^{d-2}G_p(x)
&=\frac{1}{(2\pi)^{d/2}\sqrt{\det\Sigma}}
\int_0^\infty t^{-d/2}
\exp\!\left(-\frac{e^{\mathsf T}\Sigma^{-1}e}{2t}\right)dt+o(1)\\
&=\frac{\Gamma(d/2-1)}{2\pi^{d/2}\sqrt{\det\Sigma}}
\bigl(e^{\mathsf T}\Sigma^{-1}e\bigr)^{1-d/2}+o(1).
\end{aligned}$$</div>
<p>The error is uniform in direction, and the leading expression is positive and bounded away from zero on the unit sphere. This proves the equivalent for the lazy walk. The initial identity $G_q=2G_p$ and covariance scaling give it for the original walk, including periodic walks.</p>
<p>For simple nearest-neighbour walk, $\Sigma=I/d$, giving the constant $d\Gamma(d/2-1)/(2\pi^{d/2})$ in front of $\|x\|_2^{2-d}$. By <a href="/tag/94E7/">94E7</a>, the same function is the expected occupation of a critical branching random walk with this step law. This is the finite-range spatial assertion for branching random walk. Percolation comparison still requires the hypotheses of <a href="/tag/T79N/">T79N</a>; pointwise asymptotics for infinite-range step laws are a separate question.</p>



## Self-avoiding walks and their length parameter {#section-self-avoiding-law}

<a id="tag-C69U" data-assertion="definition" data-title="Uniform fixed-length self-avoiding walk and its generating functions"></a>
<p>A nearest-neighbour self-avoiding walk of length $n$ on $\mathbb Z^d$ is a path $\omega=(\omega_0,\ldots,\omega_n)$ starting at zero, with $\|\omega_{i+1}-\omega_i\|_1=1$ and all its vertices distinct. Write $c_n(x)$ for the number ending at $x$, $c_n=\sum_xc_n(x)$, and $\mathbb E_n$ for expectation under the uniform law on these $c_n$ walks. The length-zero walk is included, so $c_0(x)=\mathbf1_{\{x=0\}}$. For $z\geq0$, define</p>
<div class="math-display">$$S_z(x)=\sum_{n\geq0}c_n(x)z^n,\qquad
\chi_{\mathrm{SAW}}(z)=\sum_x S_z(x)=\sum_{n\geq0}c_nz^n.$$</div>
<p>The uniform length-$n$ law is precisely simple random walk conditioned to avoid repeated vertices up to time $n$: every nearest-neighbour path of that length has probability $(2d)^{-n}$. This is a finite-horizon conditioning. At a smaller horizon its marginal weights a prefix by its number of allowed continuations, which need not be constant. The parameter $z$ weights path length; it is not a bond-opening probability.</p>

<a id="tag-FZKO" data-assertion="proposition" data-title="The connective constant is the inverse susceptibility radius"></a>
<p>For $d\geq1$, the limit</p>
<div class="math-display">$$\mu=\lim_{n\to\infty}c_n^{1/n}
=\inf_{n\geq1}c_n^{1/n}$$</div>
<p>exists, with $d\leq\mu\leq2d-1$. Its reciprocal $z_c=\mu^{-1}$ satisfies</p>
<div class="math-display">$$\chi_{\mathrm{SAW}}(z)&lt;\infty\quad(0\leq z&lt;z_c),
\qquad \chi_{\mathrm{SAW}}(z)=\infty\quad(z\geq z_c).$$</div>
<p><em>Proof.</em> Splitting a self-avoiding walk after $m$ steps gives an injective map to a pair of self-avoiding walks of lengths $m,n$, after translating the second piece to zero. Their possible intersection only reduces the number of concatenations. Thus $c_{m+n}\leq c_mc_n$. For fixed $k$, write $n=qk+r$, $0\leq r&lt;k$, to obtain $c_n\leq c_k^qc_r$. Taking upper limits of $n$th roots, then the infimum over $k$, proves the limit formula. Walks taking only positive coordinate steps give $c_n\geq d^n$. Avoidance of an immediate reversal gives $c_n\leq2d(2d-1)^{n-1}$ for $n\geq1$, proving the bounds on $\mu$.</p>
<p>The root test gives convergence below $z_c$. At $z_c$, the infimum formula gives $c_nz_c^n\geq1$ for every $n$, so the series diverges there and at every larger $z$. The same path-count bound shows that the probability of simple random walk avoiding repetitions through time $n$ is at most $((2d-1)/(2d))^{n-1}$, which tends to zero. Conditioning on eternal avoidance therefore cannot be defined by dividing by the probability of that event.</p>

## Diffusion in the self-avoiding model {#section-self-avoiding-diffusion}

<a id="tag-C2IS" data-assertion="theorem" data-title="High-dimensional self-avoiding diffusion and the susceptibility singularity"></a>
<p>For nearest-neighbour self-avoiding walk on $\mathbb Z^d$ with $d\geq5$, there are constants $A,D&gt;0$ such that</p>
<div class="math-display">$$c_n\sim A\mu^n,\qquad \mathbb E_n\|\omega_n\|_2^2\sim Dn.$$</div>
<p>Moreover, under the uniform length-$n$ law, the path obtained by linearly interpolating $n^{-1/2}\omega_k$ at times $k/n$ converges in distribution in $C([0,1],\mathbb R^d)$ to a nondegenerate isotropic Brownian motion. These are the Hara–Slade lace-expansion theorems, stated in <a href="https://www2.math.kyushu-u.ac.jp/~hara/papers/hara_slade_nato93.pdf">Theorems 2.1 and 2.4 of their account, pp. 91–92</a>. We take these model-specific results as cited inputs. In particular, the mean-square assertion is a separate part of that input, not an inference from weak convergence alone.</p>
<p>For $0&lt;z&lt;z_c$, define the second-moment length by</p>
<div class="math-display">$$\xi_2(z)^2=
\frac{\sum_x\|x\|_2^2S_z(x)}{\chi_{\mathrm{SAW}}(z)}.$$</div>
<p>With this convention, the following consequences have the same $A,D$:</p>
<div class="math-display">$$\chi_{\mathrm{SAW}}(z)\sim\frac{A}{1-z/z_c},
\qquad \xi_2(z)^2\sim\frac{D}{1-z/z_c}
\qquad(z\uparrow z_c).$$</div>
<p><em>Derivation of the generating-function consequences.</em> Put $r=\mu z$. Since $a_n=c_n\mu^{-n}\to A$, splitting a series at a fixed index and bounding its tail between $A-\varepsilon$ and $A+\varepsilon$ gives</p>
<div class="math-display">$$(1-r)\sum_{n\geq0}a_nr^n\longrightarrow A.$$</div>
<p>Similarly $b_n=c_n\mu^{-n}\mathbb E_n\|\omega_n\|_2^2$ satisfies $b_n/n\to AD$. The same argument, now using $\sum_{n\geq0}nr^n=r/(1-r)^2$, gives</p>
<div class="math-display">$$(1-r)^2\sum_{n\geq0}b_nr^n\longrightarrow AD.$$</div>
<p>Tonelli identifies the second series with $\sum_x\|x\|_2^2S_z(x)$; it is finite for $z&lt;z_c$ because $\|\omega_n\|_2\leq n$ and the root test applies. Dividing the two asymptotics proves the claims. They establish diffusive spatial order and the susceptibility singularity for this specified self-avoiding model. The bubble calculation for unrestricted walks does not itself supply the cited lace-expansion input, and no dimension-four logarithmic correction is asserted here.</p>

## Percolation models with Gaussian spatial decay {#section-lace-spatial-models}

<a id="tag-BSI3" data-assertion="theorem" data-title="Critical two-point asymptotics for nearest-neighbour and spread-out percolation"></a>
<p>Consider either of the following independent bond models, parametrized by the common opening probability $q$ of each allowed edge:</p>
<ul><li>Nearest-neighbour bonds on $\mathbb Z^d$, with $d\geq11$.</li>
<li>Bonds $\{x,y\}$ with $0&lt;\|x-y\|_\infty\leq L$, where $d&gt;6$ and the integer $L\geq L_0(d)$ is sufficiently large.</li></ul>
<p>For each fixed model, let $q_c$ be its critical opening probability and $\tau(x)=\mathbb P_{q_c}(0\leftrightarrow x)$. There is a constant $a&gt;0$ such that, along arbitrary lattice points with $\|x\|_2\to\infty$,</p>
<div class="math-display">$$\tau(x)\sim a\|x\|_2^{2-d}.$$</div>
<p><em>Idea of the proof (cited result).</em> Both cases come from the <a href="/articles/lace-expansion/">lace expansion</a> of the two-point function $\tau_q(x)=\mathbb P_q(0\leftrightarrow x)$. Let $J$ be the indicator of the allowed nonzero displacements. For $q&lt;q_c$ the expansion writes $\tau_q$ as the solution of a convolution equation $\tau_q=\delta_0+\Pi_q+(\delta_0+\Pi_q)*qJ*\tau_q$, where $\Pi_q$ is an alternating sum of explicit diagrams (Hara and Slade, 1990). A bootstrap argument bounds these diagrams by bubbles and triangles of $\tau_q$, uniformly in $q&lt;q_c$; it closes when the nearest-neighbour dimension or the spread-out range $L$ is large, and the bounds pass to $q_c$ by monotone limits. At $q_c$ the diagram estimates give spatial decay of $\Pi_{q_c}$ faster than $\|x\|_2^{-d-2}$. A deconvolution theorem for such equations then identifies $\tau_{q_c}$, up to a constant factor and a smaller error, with the Green function of the walk whose steps are uniform on the allowed displacements, and that Green function behaves like $\|x\|_2^{2-d}$ by the <a href="/tag/02EB/">finite-range Green asymptotic</a>. Hara, van der Hofstad and Slade carry out the deconvolution in $x$-space for the spread-out models. For nearest-neighbour bonds the asymptotic is Hara's theorem (2008), whose diagrammatic hypotheses Fitzner and van der Hofstad verify for $d\geq11$ by a non-backtracking lace expansion with computer-assisted numerical bounds.</p>
<p><em>References and parameter conversion.</em> The lace expansion for percolation is due to T. Hara and G. Slade, <em>Mean-field critical behaviour for percolation in high dimensions</em>, Comm. Math. Phys. 128 (1990). The nearest-neighbour case is Theorem 1.4 of R. Fitzner and R. van der Hofstad, <a href="https://rhofstad.win.tue.nl/PercPaper_fin.pdf"><em>Mean-field behavior for nearest-neighbor percolation in $d&gt;10$</em></a>, Electron. J. Probab. 22 (2017), combined with T. Hara, <em>Decay of correlations in nearest-neighbor self-avoiding walk, percolation, lattice trees and animals</em>, Ann. Probab. 36 (2008). The spread-out case is the box-kernel case of Definition 1.1 and Theorem 1.2 of T. Hara, R. van der Hofstad and G. Slade, <a href="https://rhofstad.win.tue.nl/hara-hofstad-slade.pdf"><em>Critical two-point functions and the lace expansion for spread-out high-dimensional percolation and related models</em></a>, Ann. Probab. 31 (2003). That paper uses the uniform box kernel $D_L(x)=(2L+1)^{-d}\mathbf1_{\{\|x\|_\infty\leq L\}}$, and a bond between distinct sites has probability $pD_L(y-x)$, so the opening probability $q$ of the statement is $q=p/(2L+1)^d$. The mass assigned to $D_L(0)$ creates no connection between distinct vertices. For fixed sufficiently large $L$, Theorem 1.2 gives the displayed equivalent by choosing its error exponent smaller than $\min\{d-6,2\}$. The paper's dimensionless correction factor $A_L$ tends to one as $L$ increases; multiplied by its positive walk-variance prefactor, it gives a positive spatial coefficient for all sufficiently large $L$. No uniformity in unbounded $L$ is needed here.</p>

## The diagrams for these percolation models {#section-lace-diagram-consequences}

<a id="tag-IDP2" data-assertion="corollary" data-title="The cited spatial estimates imply exact convolution thresholds and mean-field bounds"></a>
<p>For either model in <a href="/tag/BSI3/">BSI3</a>, and every integer $j\geq1$,</p>
<div class="math-display">$$(\tau^{*j})(0)&lt;\infty\quad\Longleftrightarrow\quad d&gt;2j.$$</div>
<p>In particular the critical triangle condition holds. The <a href="/tag/2ZI0/">triangle-condition theorem</a> therefore gives, with constants depending on the fixed model,</p>
<div class="math-display">$$\chi(q)\asymp(q_c-q)^{-1}\quad(q\uparrow q_c),\qquad
\mathbb P_{q_c}(|K_0|\geq n)\asymp n^{-1/2},\qquad
\theta(q)\asymp q-q_c\quad(q\downarrow q_c).$$</div>
<p>Here $\chi(q)=\mathbb E_q|K_0|$ and $\theta(q)=\mathbb P_q(|K_0|=\infty)$. These are two-sided comparisons, not claims of exact amplitudes.</p>
<p><em>Proof of the diagram assertion and deduction.</em> Let $G$ be the Green function of lazy nearest-neighbour walk in the same dimension. The spatial estimate <a href="/tag/02EB/">02EB</a> gives $G(x)\sim a_0\|x\|_2^{2-d}$ for some $a_0&gt;0$. Combining it with BSI3 compares $\tau$ and $G$ outside a finite set. Both functions are finite and strictly positive everywhere: the walk is irreducible, and a fixed finite allowed path has positive probability at $q_c&gt;0$. This includes the origin, where $\tau(0)=1$. Adjusting constants on the finite remaining set gives</p>
<div class="math-display">$$cG(x)\leq\tau(x)\leq CG(x)\qquad(x\in\mathbb Z^d)$$</div>
<p>for $0&lt;c\leq C&lt;\infty$. Termwise comparison of the nonnegative convolution sums, as in <a href="/tag/T79N/">T79N</a>, gives</p>
<div class="math-display">$$c^j(G^{*j})(0)\leq(\tau^{*j})(0)\leq C^j(G^{*j})(0).$$</div>
<p>The Fourier argument in <a href="/tag/E9BP/">E9BP</a> applies to every integer $j\geq1$: introduce the discounted Green function, multiply its absolutely convergent transforms, and pass to the limit by monotone convergence. Its one-step symbol $\varphi(k)=\tfrac12+\tfrac1{2d}\sum_i\cos k_i$ lies in $[0,1]$ and satisfies $1-\varphi(k)\asymp\|k\|_2^2$ near zero. Hence</p>
<div class="math-display">$$(G^{*j})(0)=\frac1{(2\pi)^d}\int_{[-\pi,\pi]^d}
(1-\varphi(k))^{-j}\,dk&lt;\infty
\quad\Longleftrightarrow\quad d&gt;2j.$$</div>
<p>All identities allow infinity. This proves the criterion, and the case $j=3$ gives the triangle condition since both model families have $d&gt;6$. Applying 2ZI0 gives the three comparisons. Its cluster-tail estimate also yields $\theta(q_c)=0$ and $\chi(q_c)=\infty$. Thus the Gaussian comparison has a rigorous model-specific realization in these ranges; the missing input was the spatial lace-expansion theorem, not a replacement of percolation by an independent branching walk.</p>



## A transition estimate for long jumps {#section-stable-transition-input}

<a id="tag-48GR" data-assertion="theorem" data-title="The Bass–Levin transition estimate for comparable power-law conductances"></a>
<p>Let $d\geq1$, $0&lt;\alpha&lt;2$, and $C_{xy}=C_{yx}$, with $C_{xx}=0$ and</p>
<div class="math-display">$$\kappa^{-1}|x-y|^{-d-\alpha}\leq C_{xy}\leq\kappa|x-y|^{-d-\alpha}\quad(x\ne y),\qquad
P(x,y)=\frac{C_{xy}}{\sum_zC_{xz}}.$$</div>
<p>Distances are Euclidean. There are $0&lt;c_1\leq c_2&lt;\infty$ such that</p>
<div class="math-display">$$P^n(x,y)\leq c_2 H_n(x,y)\quad(n\geq1),\qquad
P^n(x,y)\geq c_1 H_n(x,y)\quad(n\geq2),$$</div>
<p>where $H_n(x,y)=\min\{n^{-d/\alpha},n|x-y|^{-d-\alpha}\}$ and $H_n(x,x)=n^{-d/\alpha}$. The lower bound also holds at $n=1$ off the diagonal.</p>
<p>This is Theorem 1.1, equations (1.1)–(1.4), of R. F. Bass and D. A. Levin, <a href="https://pages.uoregon.edu/dlevin/pubs/sym.pdf"><em>Transition probabilities for symmetric jump processes</em></a>, Trans. Amer. Math. Soc. 354 (2002).</p>
<p><em>Idea of the proof (cited result).</em> The two-sided bounds on $C_{xy}$ compare the Dirichlet form of the chain with that of the translation-invariant chain with conductances $|x-y|^{-d-\alpha}$, whose Fourier symbol is comparable to $|k|^\alpha$ near zero; this gives a Nash inequality and hence the on-diagonal bound of order $n^{-d/\alpha}$.</p>
<p>For the off-diagonal upper bound one removes the jumps longer than a scale $\rho$. The truncated chain satisfies a spatial bound that decays exponentially in $|x-y|/\rho$, and the paths that make a removed jump contribute at most $Cn\rho^{-d-\alpha}$ to $P^n(x,y)$. A single choice of $\rho$ gives the term $n|x-y|^{-d-\alpha}$ only up to a power of $\log(|x-y|^\alpha/n)$ when $n$ is much smaller than $|x-y|^\alpha$; the sharp bound removes this logarithm.</p>
<p>For the lower bound, exit-time estimates show that the chain started at $x$ stays within distance of order $n^{1/\alpha}$ of $x$ up to time $n/2$ with probability bounded below, and a Harnack inequality gives the near-diagonal bound: $P^m(z,y)$ is at least a constant times $n^{-d/\alpha}$ when $n/2\leq m\leq n$ and $|z-y|$ is at most of order $n^{1/\alpha}$. When $|x-y|$ is much larger than $n^{1/\alpha}$, the off-diagonal lower bound is the product of three factors: of order $n$ times at which the chain can jump; probability of order $n^{d/\alpha}|x-y|^{-d-\alpha}$ that a jump from near $x$ lands in the ball of radius $n^{1/\alpha}$ about $y$; and probability of order $n^{-d/\alpha}$ of then being at $y$ at time $n$. The product is of order $n|x-y|^{-d-\alpha}$. The diagonal exception at $n=1$ is forced by $C_{xx}=0$. The Harnack inequality is that of R. F. Bass and D. A. Levin, <em>Harnack inequalities for jump processes</em>, Potential Anal. 17 (2002).</p>

## Summing time before space {#section-stable-potentials}

<a id="tag-UQEK" data-assertion="theorem" data-title="Long-range Green potentials and their exact dimensional thresholds"></a>
<p>Under 48GR, let $G(x,y)=\sum_{n\geq0}P^n(x,y)$. For each integer $j\geq1$, define the nonnegative extended kernel</p>
<div class="math-display">$$D_j(x,y)=\sum_{z_1,\ldots,z_{j-1}}G(x,z_1)G(z_1,z_2)\cdots G(z_{j-1},y),\qquad D_1=G.$$</div>
<p>Then</p>
<div class="math-display">$$D_j(x,y)=\sum_{n\geq0}\binom{n+j-1}{j-1}P^n(x,y).$$</div>
<p>If $d&gt;j\alpha$, the kernel is finite and, uniformly in $x,y$,</p>
<div class="math-display">$$D_j(x,y)\asymp(1+|x-y|)^{j\alpha-d}.$$</div>
<p>If $d\leq j\alpha$, it is infinite for every pair. In particular the walk is transient precisely when $d&gt;\alpha$. In that range, with $T_y=\inf\{n\geq0:X_n=y\}$,</p>
<div class="math-display">$$\mathbb P_x(T_y&lt;\infty)=\frac{G(x,y)}{G(y,y)}\asymp(1+|x-y|)^{\alpha-d}.$$</div>
<p><em>Proof.</em> Expand every Green kernel into its time series. For fixed nonnegative times $n_1,\ldots,n_j$, summing the intermediate states gives $P^{n_1+\cdots+n_j}(x,y)$ by the Markov composition rule. There are $\binom{n+j-1}{j-1}$ such time vectors of total $n$. Tonelli justifies the rearrangement, whether finite or infinite.</p>
<p>For $x\ne y$, put $R=|x-y|\geq1$. The transition estimate changes scale at $n=R^\alpha$, and the binomial coefficient is comparable to $n^{j-1}$ for $n\geq1$. When $d&gt;j\alpha$,</p>
<div class="math-display">$$\begin{aligned}
D_j(x,y)&\leq C\left[R^{-d-\alpha}\sum_{1\leq n\leq R^\alpha}n^j
+\sum_{n&gt;R^\alpha}n^{j-1-d/\alpha}\right]\\
&\leq C'R^{j\alpha-d}.
\end{aligned}$$</div>
<p>For the lower bound, sum over integers between $N$ and $2N$, where $N=\max\{2,\lceil R^\alpha\rceil\}$. Each transition probability is at least a constant times $R^{-d}$, each time weight is at least a constant times $R^{\alpha(j-1)}$, and there are at least a constant times $R^\alpha$ terms. Constants absorb the bounded range near $R=1$. On the diagonal, the term $n=0$ supplies a lower bound of one and the remaining series is bounded uniformly by $C\sum_{n\geq1}n^{j-1-d/\alpha}$.</p>
<p>If $d\leq j\alpha$, fix any $x,y$ and use the lower transition bound for $n\geq\max\{2,|x-y|^\alpha\}$. The time series dominates a positive multiple of $\sum n^{j-1-d/\alpha}$, which diverges. This also handles the critical equality; it is not obtained by substituting an endpoint into a convergent-series estimate.</p>
<p>Finally, the strong Markov property at $T_y$ decomposes the expected visits to $y$ as $\mathbb P_x(T_y&lt;\infty)G(y,y)$. The diagonal Green function lies between one and a uniform finite constant in the transient range. Division gives the hitting formula and its bounds.</p>
<p>The measure $w(x)=\sum_zC_{xz}$ is bounded above and below by positive constants, and $w(x)P(x,y)=w(y)P(y,x)$. Consequently $w(x)G(x,y)=w(y)G(y,x)$. Thus $D_2(x,x)$ is comparable to $\sum_yG(x,y)^2$ even though $G$ need not be symmetric with respect to counting measure. The bubble and triangle thresholds are $d&gt;2\alpha$ and $d&gt;3\alpha$. These are walk diagrams; no percolation comparison is supplied by reversibility or by the transition theorem.</p>

## An exact radial tail and its local limit {#section-stable-local-limit}

<a id="tag-7C2W" data-assertion="proposition" data-title="An exact radial power-law step tail gives a uniform stable local limit"></a>
<p>Let $p$ be a symmetric probability mass function on $\mathbb Z^d$, with $p(0)=0$, $p(z)&gt;0$ for $z\ne0$, and</p>
<div class="math-display">$$p(z)|z|^{d+\alpha}\longrightarrow c\in(0,\infty)\qquad(|z|\to\infty),\qquad0&lt;\alpha&lt;2.$$</div>
<p>Here and below $|\cdot|$ is Euclidean. Put</p>
<div class="math-display">$$v=c\int_{\mathbb R^d}\frac{1-\cos u_1}{|u|^{d+\alpha}}\,du\in(0,\infty),\qquad
g_v(x)=\frac1{(2\pi)^d}\int_{\mathbb R^d}e^{-ik\cdot x-v|k|^\alpha}\,dk.$$</div>
<p>Then $\widehat p(k)=1-v|k|^\alpha+o(|k|^\alpha)$ uniformly in direction, $g_v$ is a continuous radial probability density, and</p>
<div class="math-display">$$\sup_{x\in\mathbb Z^d}\left|n^{d/\alpha}p^{*n}(x)-g_v(x/n^{1/\alpha})\right|\longrightarrow0.$$</div>
<p><em>Proof.</em> The integral defining $v$ is finite: near zero use $1-\cos u_1\leq |u|^2/2$, and at infinity use the bound two. The restrictions $\alpha&lt;2$ and $\alpha&gt;0$ give integrability in the two regions. The integrand is positive on a set of positive measure.</p>
<p>Write $k=\rho e$, with $|e|=1$. Since $p(z)|z|^{d+\alpha}$ is bounded and tends to $c$, the middle part of</p>
<div class="math-display">$$\rho^{-\alpha}(1-\widehat p(\rho e))
=\rho^d\sum_{z\ne0}\bigl(p(z)|z|^{d+\alpha}\bigr)
\frac{1-\cos(e\cdot\rho z)}{|\rho z|^{d+\alpha}}$$</div>
<p>over $\delta\leq|\rho z|\leq M$ converges to the corresponding integral with coefficient $c$. Convergence is uniform over unit $e$: on this fixed annulus the integrands form an equicontinuous bounded family, so a finite uniform approximation reduces the assertion to ordinary Riemann sums. The inner and outer sums are bounded uniformly by $C\delta^{2-\alpha}$ and $CM^{-\alpha}$, respectively, by lattice shell counting. The integrals obey the same bounds. Let $\rho\downarrow0$, then $\delta\downarrow0$ and $M\uparrow\infty$. Rotational invariance makes the limiting integral independent of $e$, proving the expansion.</p>
<p>There are no other points of modulus one for $\widehat p$ on the frequency torus. Equality in the triangle inequality would force all phases $e^{ik\cdot z}$, $z\ne0$, to agree. Comparing $e_i$ and $2e_i$ then forces each coordinate phase to equal one. Compactness gives $|\widehat p|\leq\eta&lt;1$ outside any fixed neighbourhood of zero. Near zero the expansion gives $|\widehat p(k)|\leq e^{-a|k|^\alpha}$ for some $a&gt;0$.</p>
<p>Extend $\widehat p(t/n^{1/\alpha})^n$ by zero outside the rescaled torus. It converges pointwise to $e^{-v|t|^\alpha}$. On the rescaled small neighbourhood the absolute value is bounded by $e^{-a|t|^\alpha}$; the complementary integral is at most $Cn^{d/\alpha}\eta^n$. Thus convergence holds in $L^1(\mathbb R^d)$. Fourier inversion gives the uniform local limit. The same characteristic-function convergence and the continuity theorem identify $e^{-v|t|^\alpha}$ as the characteristic function of a probability law. Its integrability gives density $g_v$; rotational invariance gives radiality.</p>

## The stable Green equivalent {#section-stable-green-equivalent}

<a id="tag-NMTU" data-assertion="theorem" data-title="The spatial Green equivalent for an exact radial long-range step law"></a>
<p>Under 7C2W, if $d&gt;\alpha$, then uniformly along lattice directions,</p>
<div class="math-display">$$G_p(x)=\sum_{n\geq0}p^{*n}(x)
\sim\frac{\Gamma((d-\alpha)/2)}{2^\alpha\pi^{d/2}\Gamma(\alpha/2)\,v}|x|^{\alpha-d}
\qquad(|x|\to\infty).$$</div>
<p>For $d\leq\alpha$, $G_p(x)=\infty$ at every $x$. If a holding probability $h\in[0,1)$ is added, so $p_h=h\delta_0+(1-h)p$, then $G_{p_h}=G_p/(1-h)$; the displayed equivalent uses $v_h=(1-h)v$.</p>
<p><em>Proof.</em> Positivity at each nonzero lattice point and the tail equivalent give global two-sided comparison with $|z|^{-d-\alpha}$ after adjusting constants on a finite set. Apply the <a href="/tag/48GR/">Bass–Levin estimate</a> with $C_{xy}=p(y-x)$, whose row sum is one. The recurrence statement and finiteness in the transient range follow from the <a href="/tag/UQEK/">long-range Green potential bounds</a>.</p>
<p>Assume $d&gt;\alpha$, write $R=|x|$ and $e=x/R$, and fix $0&lt;a&lt;b&lt;\infty$. The local limit gives, uniformly in unit directions,</p>
<div class="math-display">$$R^{d-\alpha}\sum_{aR^\alpha\leq n\leq bR^\alpha}p^{*n}(x)
\longrightarrow\int_a^b t^{-d/\alpha}g_v(e/t^{1/\alpha})\,dt.$$</div>
<p>The error is uniform because the local-limit error is uniform in the lattice point and tends to zero throughout this time interval. The remaining Riemann sums are uniform in $e$ by continuity on a compact set. The cited transition bound controls the omitted times:</p>
<div class="math-display">$$\begin{aligned}
\limsup_{R\to\infty}R^{d-\alpha}\sum_{1\leq n&lt;aR^\alpha}p^{*n}(x)&\leq Ca^2,\\
\limsup_{R\to\infty}R^{d-\alpha}\sum_{n&gt;bR^\alpha}p^{*n}(x)&\leq Cb^{1-d/\alpha}.
\end{aligned}$$</div>
<p>The first estimate sums $CnR^{-d-\alpha}$, and the second sums $Cn^{-d/\alpha}$. Since $x\ne0$, generation zero contributes nothing. Both bounds vanish when $a\downarrow0$ and $b\uparrow\infty$.</p>
<p>It remains to identify the integral, including its constant. Let $g_{vt}(x)=t^{-d/\alpha}g_v(x/t^{1/\alpha})$ and $U(x)=\int_0^\infty g_{vt}(x)\,dt$. Passing the transition upper bound through the local limit gives</p>
<div class="math-display">$$g_{vt}(x)\leq C\min\{t^{-d/\alpha},t|x|^{-d-\alpha}\}\qquad(x\ne0).$$</div>
<p>Hence $U$ is continuous off zero and bounded by $C|x|^{\alpha-d}$. Its Fourier transform, in the sense of integration against Schwartz test functions, is $1/(v|k|^\alpha)$. Indeed, integrating $e^{-vt|k|^\alpha}$ in $t$ gives this function, and the interchange is justified by $\int |\widehat f(k)||k|^{-\alpha}\,dk&lt;\infty$, since $d&gt;\alpha$. The corresponding spatial integrals converge by the bound on $U$.</p>
<p>The Gamma identity</p>
<div class="math-display">$$|k|^{-\alpha}=\frac1{\Gamma(\alpha/2)}\int_0^\infty s^{\alpha/2-1}e^{-s|k|^2}\,ds$$</div>
<p>and Gaussian Fourier inversion therefore identify, for $x\ne0$,</p>
<div class="math-display">$$\begin{aligned}
U(x)&=\frac1{v\Gamma(\alpha/2)}\int_0^\infty s^{\alpha/2-1}(4\pi s)^{-d/2}e^{-|x|^2/(4s)}\,ds\\
&=\frac{\Gamma((d-\alpha)/2)}{2^\alpha\pi^{d/2}\Gamma(\alpha/2)\,v}|x|^{\alpha-d}.
\end{aligned}$$</div>
<p>Both sides are locally integrable and continuous off zero, so their equality as distributions gives pointwise equality there. Substituting $|e|=1$ into the time-sum limit proves the equivalent, including uniformity in direction.</p>
<p>For the holding modification, expand $p_h^{*n}$ binomially and use Tonelli. For each number $m$ of actual steps,</p>
<div class="math-display">$$\sum_{n\geq m}\binom nm h^{n-m}(1-h)^m=\frac1{1-h},$$</div>
<p>which proves the exact Green identity, including extended values. This also checks the normalization of the leading constant.</p>
<p>For example, normalizing $p(z)\propto |z|^{-d-\alpha}$, $z\ne0$, gives the spatial power $\alpha-d$ for every $0&lt;\alpha&lt;\min\{2,d\}$. By <a href="/tag/94E7/">the occupation identity</a>, this is also the expected occupation of a critical branching random walk with these steps. The Gaussian power therefore cannot hold for arbitrary steps. The heat-kernel input here remains external; the stable local limit and time-summation argument are written proofs. The endpoint $\alpha=2$, nonradial leading amplitudes and percolation spatial equivalents require further results.</p>



## The marginal step law {#section-marginal-step-law}

<p>The <a href="/tag/1POM/">long-range diagram thresholds</a> include the endpoint $\alpha=2$. At this endpoint the following concrete step law without holding has spatial equivalents, including at the threshold. Fix $L\geq1$ and set</p>
<div class="math-display">$$D_L(0)=0,\qquad D_L(x)=\frac{(|x|\vee L)^{-d-2}}{Z_L}\quad(x\ne0),\qquad Z_L=\sum_{y\ne0}(|y|\vee L)^{-d-2}.$$</div>
<p>Distances are Euclidean. Throughout the walk calculations $L$ is fixed; constants and errors may depend on it.</p>

## The logarithmic Gaussian scale {#section-marginal-local-limit}

<a id="tag-V7FQ" data-assertion="proposition" data-title="The marginal symbol constant and uniform Gaussian local limit"></a>
<p>For $D_L$ above, let $s_{d-1}=2\pi^{d/2}/\Gamma(d/2)$ and $v_L=s_{d-1}/(2dZ_L)$. Then, uniformly in direction,</p>
<div class="math-display">$$1-\widehat D_L(k)=v_L|k|^2\log(1/|k|)+O_L(|k|^2)\qquad(k\to0).$$</div>
<p>With $a_n=\sqrt{n\log n}$ for $n\geq2$, and</p>
<div class="math-display">$$g_v(u)=(2\pi v_L)^{-d/2}\exp\!\left(-\frac{|u|^2}{2v_L}\right),$$</div>
<p>one has</p>
<div class="math-display">$$\sup_{x\in\mathbb Z^d}\left|a_n^dD_L^{*n}(x)-g_v(x/a_n)\right|\longrightarrow0,\qquad
\sup_xD_L^{*n}(x)\leq C_L(n\log n)^{-d/2}\quad(n\geq2).$$</div>
<p><em>Proof.</em> Comparing $|z|^{-d}$ on lattice cubes with its integral gives</p>
<div class="math-display">$$\sum_{0&lt;|z|\leq R}|z|^{-d}=s_{d-1}\log R+O(1).$$</div>
<p>Indeed, outside a fixed ball the error on the cube at $z$ is $O(|z|^{-d-1})$, whose lattice sum converges. Cubes meeting the outer sphere contribute $O(R^{-1})$ to the discrepancy of the domains. Reflection and coordinate-permutation symmetry therefore give</p>
<div class="math-display">$$\sum_{|z|\leq R}D_L(z)z_i z_j
=\delta_{ij}\left(\frac{s_{d-1}}{dZ_L}\log R+O_L(1)\right).$$</div>
<p>The modification inside radius $L$ affects only the bounded term. Write $\rho=|k|$ and expand $1-\cos(k\cdot z)$ through its quadratic term for $|z|\leq\rho^{-1}$. The remainder is at most</p>
<div class="math-display">$$C\rho^4\sum_{|z|\leq\rho^{-1}}D_L(z)|z|^4=O_L(\rho^2),$$</div>
<p>and the omitted tail is bounded by $2\sum_{|z|&gt;\rho^{-1}}D_L(z)=O_L(\rho^2)$. The covariance identity proves the symbol expansion with the stated constant.</p>
<p>Put $\varphi=\widehat D_L$. Every nonzero lattice point has positive mass. As in the proof of the <a href="/tag/7C2W/">stable local limit for an exact radial tail</a>, equality $|\varphi(k)|=1$ forces the phases at $e_i$ and $2e_i$ to coincide, hence $k=0$ on the torus. Choose $\delta&lt;e^{-1/2}$ small enough that $\varphi$ is positive and</p>
<div class="math-display">$$|\varphi(k)|\leq\exp\{-c|k|^2\log(1/|k|)\}\qquad(0&lt;|k|\leq\delta).$$</div>
<p>For fixed $t$, the expansion and $\log a_n/\log n\to1/2$ imply</p>
<div class="math-display">$$\varphi(t/a_n)^n\longrightarrow e^{-v_L|t|^2/2}.$$</div>
<p>This convergence holds in $L^1$ after extending the left side by zero outside the rescaled torus. To see the needed uniform tail control, fix $0&lt;\eta&lt;1$. On $|t|\leq a_n^\eta$, the preceding exponential bound is at most $e^{-c_\eta|t|^2}$ for all large $n$. On $a_n^\eta&lt;|t|\leq\delta a_n$, monotonicity of $r^2\log(1/r)$ on $(0,\delta]$ bounds it by $e^{-c_\eta a_n^{2\eta}}$. The integral over this region tends to zero even after its volume factor $O(a_n^d)$. Finally, outside the original $\delta$-ball, compactness gives $|\varphi|\leq q&lt;1$, so the remaining integral is at most $O(a_n^dq^n)$. Dominated convergence on the first region completes the $L^1$ argument. Fourier inversion yields the uniform local limit; boundedness of $g_v$ gives the displayed upper bound, after adjusting the constant for finitely many times.</p>

## An off-diagonal transition bound {#section-marginal-transition-bound}

<p>The <a href="/tag/V7FQ/">uniform local limit</a> describes $D_L^{*n}(x)$ when $n$ is of order $|x|^2/\log|x|$ or larger. For shorter times the following bound controls $D_L^{*n}(x)$; it handles the times $n\ll|x|^2/\log|x|$ in the <a href="/tag/CEVT/">marginal Green potential equivalents</a>.</p>

<a id="tag-G12U" data-assertion="theorem" data-title="The marginal transition bound for the clipped power-law walk"></a>
<p>For this law, there is $C_L&lt;\infty$ such that</p>
<div class="math-display">$$D_L^{*n}(x)\leq C_L\frac{n\log(2+|x|)}{(1+|x|)^{d+2}}\qquad(n\geq1,\ x\ne0).$$</div>
<p>This is the fixed-$L$ form of (1.13), with example (1.14), of L.-C. Chen and A. Sakai, <a href="https://arxiv.org/abs/1808.06789v3"><em>Critical two-point function for long-range models with power-law couplings: the marginal case for $d\ge d_c$</em></a> (2019).</p>
<p><em>Idea of the proof.</em> Let $t=|x|$ be large and cut the steps at length $t/K$ for a fixed integer $K$. A path that uses a step longer than $t/K$ costs one factor $D_L(z)\leq Z_L^{-1}(t/K)^{-d-2}$, and there are $n$ choices for the time of that step: this gives $Cn\,t^{-d-2}$. A path made of short steps needs at least $K$ of them, and one of its two halves must travel distance of order $t$ in a fixed coordinate. The truncated steps have variance of order $\log t$, so a Bennett-type exponential bound for bounded variables makes this probability at most a high power of $u=n\log t/t^2$, while the other half contributes the local bound $(n\log n)^{-d/2}$. The logarithm in the claim comes from the same variance. At the crossover time $n\asymp t^2/\log t$, where $u$ is of order one, only the local bound is available, and it is $(n\log n)^{-d/2}\asymp t^{-d}$, while $nt^{-d-2}\asymp t^{-d}/\log t$; so the factor $\log(2+|x|)$ cannot be dropped. For larger $n$ the local bound alone has the required size.</p>
:::details Proof
<p>Write $D=D_L$ and let $X_1,X_2,\ldots$ be independent with law $D$, $S_n=X_1+\cdots+X_n$, so that $D^{*n}(x)=\mathbb P(S_n=x)$. Constants $C,c_1,c_2,\ldots$ below depend only on $d$ and $L$. We use four facts.</p>
<p>(a) Since $|z|\vee L\geq|z|$, one has $D(z)\leq Z_L^{-1}|z|^{-d-2}$ for every $z\ne0$. Also $D$ is invariant under changing the sign of any coordinate.</p>
<p>(b) For $r\geq1$ and each coordinate $j$,</p>
<div class="math-display">$$\sum_{|z|\leq r}D(z)z_j^2\leq Z_L^{-1}\sum_{0&lt;|z|\leq r}|z|^{-d}\leq c_1\log(2+r).$$</div>
<p>Indeed, nonzero lattice points have $|z|\geq1$; the shell $2^{i-1}&lt;|z|\leq2^i$ contains at most $(2^{i+1}+1)^d\leq 3^d2^{id}$ points, each contributing less than $2^{-(i-1)d}$, so each shell contributes at most $6^d$, and the shells with $0\leq i\leq\lceil\log_2r\rceil$ cover the sum.</p>
<p>(c) By the uniform local limit, $\sup_yD^{*k}(y)\leq C_L(k\log k)^{-d/2}$ for $k\geq2$.</p>
<p>(d) (A Bennett-type exponential bound.) Let $Y_1,\ldots,Y_m$ be independent copies of a real variable $Y$ with $\mathbb EY=0$, $|Y|\leq r$ and $\mathbb EY^2\leq\sigma^2$, where $r,\sigma^2&gt;0$. Then for $s&gt;0$,</p>
<div class="math-display">$$\mathbb P(Y_1+\cdots+Y_m\geq s)\leq\left(\frac{e\,m\sigma^2}{sr}\right)^{s/r}.$$</div>
<p>To see this, note that $\psi(u)=(e^u-1-u)/u^2=\int_0^1(1-v)e^{uv}\,dv$ is nondecreasing on $\mathbb R$. For $\lambda&gt;0$, $\lambda Y\leq\lambda r$ gives $e^{\lambda Y}\leq1+\lambda Y+\lambda^2Y^2\psi(\lambda r)$, hence</p>
<div class="math-display">$$\mathbb Ee^{\lambda Y}\leq1+\frac{\sigma^2(e^{\lambda r}-1-\lambda r)}{r^2}\leq\exp\!\left(\frac{\sigma^2e^{\lambda r}}{r^2}\right).$$</div>
<p>If $m\sigma^2\geq sr$ the claimed bound exceeds one. Otherwise take $\lambda=r^{-1}\log(sr/(m\sigma^2))&gt;0$ in Markov's inequality: $\mathbb P(\sum Y_i\geq s)\leq\exp(-\lambda s+m\sigma^2e^{\lambda r}/r^2)$, and $m\sigma^2e^{\lambda r}/r^2=s/r$, which gives the bound.</p>
<p><em>Reduction.</em> Fix an integer $K\geq\max\{4,\ 2\sqrt d\,(d/2+2)\}$, which makes the exponent in (d) at least $d/2+2$ below; put $c_2=4e\sqrt d\,Kc_1$, the constant that (d) produces, and $\delta=1/c_2$, which keeps the base of that bound at most one at small times. Choose $t_0\geq e$ with $\delta t/\log t\geq1$ and $(\log t)^{d/2+1}\leq t$ for $t\geq t_0$. Let $t=|x|$. If $1\leq t&lt;t_0$, then $D^{*n}(x)\leq1$ while the right side of the claim is at least $C_L\log3/(1+t_0)^{d+2}$, so the claim holds after enlarging $C_L$. For $t\geq t_0$ we have $1+t\leq2t$ and $\log t\leq\log(2+t)$, so it suffices to prove</p>
<div class="math-display">$$D^{*n}(x)\leq C\,\frac{n\log t}{t^{d+2}}\qquad(n\geq1,\ |x|=t\geq t_0).\tag{1}$$</div>
<p><em>Large times.</em> Suppose $n&gt;\delta t^2/\log t$. Then $n\geq t\geq e$, so $n\geq2$ and $\log n\geq\log t$, and by (c)</p>
<div class="math-display">$$D^{*n}(x)\leq C_L(n\log t)^{-d/2}
=C_L\frac{n\log t}{t^{d+2}}\cdot\frac{t^{d+2}}{(n\log t)^{1+d/2}}
\leq C_L\delta^{-1-d/2}\frac{n\log t}{t^{d+2}}.$$</div>
<p><em>Small times: one long step.</em> Now let $n\leq\delta t^2/\log t$ and put $r=t/K$. For each $i\leq n$, $S_n-X_i$ is independent of $X_i$, so by (a)</p>
<div class="math-display">$$\mathbb P(S_n=x,\ |X_i|&gt;r)=\sum_{|z|&gt;r}D(z)\,\mathbb P(S_n-X_i=x-z)\leq Z_L^{-1}r^{-d-2}=Z_L^{-1}K^{d+2}t^{-d-2}.$$</div>
<p>Summing over $i$ bounds the probability that $S_n=x$ and some step is longer than $r$ by $Z_L^{-1}K^{d+2}n\,t^{-d-2}$, which is at most the right side of (1) because $\log t\geq1$.</p>
<p><em>Small times: only short steps.</em> Let $A$ be the event that $|X_i|\leq r$ for all $i\leq n$. On $A$, $|S_n|\leq nr=nt/K$, so $\mathbb P(S_n=x,A)=0$ unless $n\geq K\geq4$; assume this. Choose a coordinate $j$ with $|x_j|\geq t/\sqrt d$; by the reflection invariance in (a) we may assume $x_j&gt;0$. Put $m=\lfloor n/2\rfloor$ and $s=x_j/2\geq t/(2\sqrt d)$. If $S_n=x$, then either $S_m$ or $S_n-S_m$ has $j$-th coordinate at least $s$. The two blocks of steps are independent. Conditioning on the first block, and then on the second, gives</p>
<div class="math-display">$$\mathbb P(S_n=x,A)\leq\mathbb P\Bigl(\textstyle\sum_{i=1}^{m}Y_i\geq s\Bigr)\sup_yD^{*(n-m)}(y)+\mathbb P\Bigl(\textstyle\sum_{i=1}^{n-m}Y_i\geq s\Bigr)\sup_yD^{*m}(y),$$</div>
<p>where $Y_i=X_i\cdot e_j\,\mathbf1_{\{|X_i|\leq r\}}$. On $A$ the $j$-th coordinate of the displacement of either block equals the sum of the $Y_i$ over that block, and these are independent copies of $Y_1$. By (a) the variables $Y_i$ are symmetric, so $\mathbb EY_i=0$; also $|Y_i|\leq r$ and, by (b), $\mathbb EY_i^2\leq\sigma^2:=c_1\log(2+r)\leq2c_1\log t$, since $t\geq e$ implies $2+t\leq t^2$. For $k=m$ and for $k=n-m$, since $k\leq n$ and $sr\geq t^2/(2\sqrt dK)$, fact (d) gives</p>
<div class="math-display">$$\mathbb P\Bigl(\textstyle\sum_{i=1}^kY_i\geq s\Bigr)\leq\bigl(c_2u\bigr)^{s/r},\qquad u=\frac{n\log t}{t^2}.$$</div>
<p>Here $c_2u\leq1$ and $s/r\geq K/(2\sqrt d)\geq d/2+2$, so this is at most $(c_2u)^{d/2+2}$. For the other factor, $n-k\geq m\geq2$ and $n-k\geq n/3$, so $\log(n-k)\geq c_0\log n$ with $c_0=\log2/\log9$ (use $\log(n-k)\geq\log2$ when $n&lt;9$ and $\log(n-k)\geq\log(n/3)\geq\tfrac12\log n$ when $n\geq9$). By (c), $\sup_yD^{*(n-k)}(y)\leq C(n\log n)^{-d/2}$. Therefore</p>
<div class="math-display">$$\mathbb P(S_n=x,A)\leq 2C\,c_2^{d/2+2}\,u\cdot f,\qquad f=(n\log n)^{-d/2}u^{d/2+1}
=n\,(\log n)^{-d/2}(\log t)^{d/2+1}t^{-d-2}.$$</div>
<p>If $n\leq t$, then $\log n\geq\log4&gt;1$ and $f\leq(\log t)^{d/2+1}t^{-d-1}\leq t^{-d}$ by the choice of $t_0$. If $n&gt;t$, then $\log n&gt;\log t$ and $f\leq n\log t\,t^{-d-2}\leq\delta t^{-d}$. In both cases $u f\leq u\,t^{-d}=n\log t/t^{d+2}$.</p>
<p>Adding the three bounds proves (1), and hence the theorem.</p>
:::

## Spatial potentials at and above the threshold {#section-marginal-potentials}

<a id="tag-CEVT" data-assertion="theorem" data-title="Marginal Green potential equivalents, including critical equality"></a>
<p>Let $G_L=\sum_{n\geq0}D_L^{*n}$ and $H_j=G_L^{*j}$ for integers $j\geq1$, with all sums understood as nonnegative extended sums. If $d&gt;2j$, then</p>
<div class="math-display">$$H_j(x)\sim
\frac{\Gamma(d/2-j)}{4^j\pi^{d/2}\Gamma(j)v_L^j}\,
\frac{|x|^{2j-d}}{(\log|x|)^j}\qquad(|x|\to\infty).$$</div>
<p>At $d=2j$ with $j\geq2$, the potential is still finite and</p>
<div class="math-display">$$H_j(x)\sim
\frac{2^{1-2j}}{\pi^jv_L^j(j-1)\Gamma(j)}
(\log|x|)^{1-j}.$$</div>
<p>Both equivalents are uniform in direction. In all remaining cases, $H_j(x)=\infty$ for every $x$. In particular, $G_L$ is finite exactly when $d&gt;2$, and in that range</p>
<div class="math-display">$$G_L(x)\sim\frac{\Gamma(d/2-1)}{4\pi^{d/2}v_L}\,
\frac{|x|^{2-d}}{\log|x|}.$$</div>
<p><em>Proof.</em> Expanding the $j$ Green factors and summing intermediate vertices first gives the same time-composition identity as in <a href="/tag/UQEK/">UQEK</a>:</p>
<div class="math-display">$$H_j(x)=\sum_{n\geq0}\binom{n+j-1}{j-1}D_L^{*n}(x).$$</div>
<p>Only the Markov composition rule and Tonelli are used in this identity, not the restriction $\alpha&lt;2$ in that earlier spatial theorem. For fixed $x$, the <a href="/tag/V7FQ/">uniform local limit</a> gives $D_L^{*n}(x)\sim g_v(0)(n\log n)^{-d/2}$. Since the binomial coefficient is asymptotic to $n^{j-1}/\Gamma(j)$, the series converges precisely when $d&gt;2j$ or $d=2j$ and $j&gt;1$. This proves finiteness or divergence at every point.</p>
<p>Suppose first that $d&gt;2j$. Write $R=|x|$ and $N_R=R^2/(v_L\log R)$. For fixed $0&lt;a&lt;b&lt;\infty$, uniformly for $a\leq t\leq b$ and $n/N_R\to t$, the local limit gives</p>
<div class="math-display">$$R^dD_L^{*n}(x)\longrightarrow(4\pi t)^{-d/2}e^{-1/(4t)}.$$</div>
<p>Here $n\log n/R^2\to2t/v_L$. The limit is independent of the direction of $x$. Applying the binomial asymptotic and a Riemann sum yields</p>
<div class="math-display">$$\frac{R^d}{N_R^j}\sum_{aN_R\leq n\leq bN_R}
\binom{n+j-1}{j-1}D_L^{*n}(x)
\longrightarrow\frac1{\Gamma(j)}\int_a^b t^{j-1}(4\pi t)^{-d/2}e^{-1/(4t)}\,dt.$$</div>
<p>The <a href="/tag/G12U/">marginal transition bound</a> and the upper bound in the uniform local limit control the omitted times separately:</p>
<div class="math-display">$$\begin{aligned}
\limsup_{R\to\infty}\frac{R^d}{N_R^j}
\sum_{1\leq n&lt;aN_R}\binom{n+j-1}{j-1}D_L^{*n}(x)&\leq C_La^{j+1},\\
\limsup_{R\to\infty}\frac{R^d}{N_R^j}
\sum_{n&gt;bN_R}\binom{n+j-1}{j-1}D_L^{*n}(x)&\leq C_Lb^{j-d/2}.
\end{aligned}$$</div>
<p>For the first estimate, sum $C_Ln^j\log R/R^{d+2}$ and use $N_R\log R/R^2=1/v_L$. For the second, sum $C_Ln^{j-1-d/2}(\log n)^{-d/2}$; for fixed $b$, $\log(bN_R)\sim2\log R$. The constants are independent of $a\in(0,1)$ and $b&gt;1$. Generation zero contributes nothing when $x\ne0$. Let $a\downarrow0$ and $b\uparrow\infty$. The substitution $u=1/(4t)$ evaluates the integral as</p>
<div class="math-display">$$\frac1{\Gamma(j)}\int_0^\infty t^{j-1}(4\pi t)^{-d/2}e^{-1/(4t)}\,dt
=\frac{\Gamma(d/2-j)}{4^j\pi^{d/2}\Gamma(j)}.$$</div>
<p>Multiplying by $N_R^j/R^d$ proves the first equivalent.</p>
<p>At $d=2j$, the dominant times are much later. Put $M_R=R^2/\log R$. The contribution of $1\leq n\leq M_R$ is $O_L((\log R)^{-j})$ by the marginal transition bound. Between $M_R$ and $R^2$, the upper bound in the uniform local limit gives the bound</p>
<div class="math-display">$$C_L\sum_{M_R&lt;n&lt;R^2}\frac1{n(\log n)^j}
=O_L\!\left(\frac{\log\log R}{(\log R)^j}\right)
=o((\log R)^{1-j}).$$</div>
<p>For $n\geq R^2$, we have $|x|/a_n\leq(2\log R)^{-1/2}$. The uniform local limit and continuity of $g_v$ at zero therefore give, uniformly throughout this range,</p>
<div class="math-display">$$\binom{n+j-1}{j-1}D_L^{*n}(x)
=\left(\frac{(2\pi v_L)^{-j}}{\Gamma(j)}+o(1)\right)
\frac1{n(\log n)^j}.$$</div>
<p>Because $j&gt;1$, the remaining sum is asymptotic to $(2\log R)^{1-j}/(j-1)$. This proves the critical constant. All estimates were independent of the direction of $x$.</p>
<p>Thus at $d=4$ the bubble potential $H_2(x)$ is asymptotic to $1/(8\pi^2v_L^2\log|x|)$, while at $d=6$ the triangle potential $H_3(x)$ is asymptotic to $1/(128\pi^3v_L^3(\log|x|)^2)$. The finite values at zero follow from the time series, not by substituting zero into these spatial equivalents.</p>

## A percolation comparison at dimension six {#section-marginal-percolation}

<a id="tag-6ZYT" data-assertion="theorem" data-title="The cited marginal percolation equivalent and its diagram consequences"></a>
<p>On $\mathbb Z^d$, open each unordered bond independently with probability $pD_L(y-x)$, where $0\leq p\leq1/\max_zD_L(z)$. For $d\geq6$ and sufficiently large $L$, <a href="https://arxiv.org/html/1808.06789v3#S1.SS2.SSS5">Chen–Sakai, Theorem 1.4, (1.36)</a> gives the cited input</p>
<div class="math-display">$$\tau_{p_c}(x)\sim\frac1{p_c}\frac{\Gamma(d/2-1)}{4\pi^{d/2}v_L}\,
\frac{|x|^{2-d}}{\log|x|}.$$</div>
<p>Here $p_c$ is the critical value of this bond-probability multiplier. The source's example (1.14) verifies its kernel assumptions. Its lace-expansion proof remains external.</p>
<p>The written deduction is that there exist $0&lt;c\leq C&lt;\infty$ such that $cG_L(x)\leq\tau_{p_c}(x)\leq CG_L(x)$ for every $x$. Indeed, the ratio tends to $1/p_c$ by CEVT and the cited equivalent. On the remaining finite set both functions are positive and finite: off the origin the single bond has positive probability, and at the origin $\tau_{p_c}(0)=1$. Adjust the constants on that set.</p>
<p>Multiplication of these bounds in the nonnegative convolution sums gives</p>
<div class="math-display">$$c^jH_j(x)\leq\tau_{p_c}^{*j}(x)\leq C^jH_j(x)\qquad(j\geq1).$$</div>
<p>Consequently the percolation potential has the same finiteness criterion and the same spatial order as $H_j$. This supplies the comparison required in <a href="/tag/T79N/">T79N</a> for this model. In particular the critical triangle is finite at $d=6$, and its potential at large $x$ is comparable to $(\log|x|)^{-2}$. The <a href="/tag/2ZI0/">mean-field triangle theorem</a> applies. No exact convolution amplitude for percolation is inferred from the comparison, and the statement makes no assertion about nearest-neighbour percolation in dimension six.</p>

## Normalizing a compounded step law {#section-compound-normalization}

<a id="tag-DTYB" data-assertion="proposition" data-title="Normalization of a polynomially compounded lattice law"></a>
<p>Let $w:\mathbb Z^d\to[0,\infty)$ be summable, with $H=\sum_{x\ne0}w(x)&gt;0$, and let $T(t)=t^{-1-\alpha/2}/\zeta(1+\alpha/2)$, $t\geq1$, for $\alpha&gt;0$. If $U(x)=w(x)/H$ and $w(0)&gt;0$, then $\sum_{t\geq1}T(t)U^{*t}$ has infinite total mass. In contrast,</p>
<div class="math-display">$$U^*(x)=\frac{\mathbf1_{\{x\ne0\}}w(x)}H,\qquad
D^*(x)=\sum_{t\geq1}T(t)(U^*)^{*t}(x)$$</div>
<p>are probability mass functions.</p>
<p><em>Proof.</em> The mass of $U$ is $m=1+w(0)/H&gt;1$. Tonelli gives mass $m^t$ for $U^{*t}$, so the mixture has mass $\sum_{t\geq1}m^tT(t)=\infty$; its summands do not even tend to zero. The mass of $U^*$ is one, hence every convolution power has mass one and the mixture has mass $\sum_tT(t)=1$.</p>
<p>For the cube density $w(x)=2^{-d}\mathbf1_{\{\|x\|_\infty\leq1\}}$, the first mass is $3^d/(3^d-1)$. This diagnoses the origin convention in <a href="/errata/chen-sakai-marginal-2019/#compound-zeta-normalization">the provisional source erratum</a>. The repair establishes normalization only; it does not establish every transition hypothesis for the compounded law. The marginal walk and percolation results above use the separate clipped power-law distribution $D_L$.</p>


## Restoring the all-lattice normalization {#section-all-lattice-compound}

<p>The punctured law in DTYB is normalized, but the correction recommended in FIXER's resolution instead includes the origin in the denominator. It restores the law used in <a href="https://arxiv.org/html/1204.1180v4">Chen–Sakai's earlier paper, Appendix A, (A.2)</a>. These are different laws; an estimate for one does not transfer to the other merely by normalization.</p>

<a id="tag-TIOJ" data-assertion="proposition" data-title="The all-lattice compound law is normalized and the cube example is irreducible and aperiodic"></a>
<p>Let $h:\mathbb R^d\to[0,\infty)$ be bounded and compactly supported. Fix $L&gt;0$ such that $H_L^0=\sum_{y\in\mathbb Z^d}h(y/L)&gt;0$, and let $\alpha&gt;0$. Then</p>
<div class="math-display">$$\widetilde U_L(x)=\frac{h(x/L)}{H_L^0},\qquad
\widetilde D_L(x)=\sum_{t\geq1}\frac{t^{-1-\alpha/2}}{\zeta(1+\alpha/2)}\widetilde U_L^{*t}(x)$$</div>
<p>are probability mass functions. If $h$ is Riemann integrable with integral one, then $H_L^0&gt;0$ for all sufficiently large $L$. For the cube density $h(u)=2^{-d}\mathbf1_{\{\|u\|_\infty\leq1\}}$ and every integer $L\geq1$, the compound law is symmetric, nondegenerate, irreducible and aperiodic. The punctured cube compound law of DTYB has these properties as well.</p>
<p><em>Proof.</em> Compact support makes the denominator a finite sum. Its positivity gives $\sum_x\widetilde U_L(x)=1$. For nonnegative summable functions $f,g$, Tonelli and translation of the inner sum give</p>
<div class="math-display">$$\sum_x(f*g)(x)=\sum_z f(z)\sum_xg(x-z)=\left(\sum_zf(z)\right)\left(\sum_xg(x)\right).$$</div>
<p>Thus every convolution power has mass one. The weights have sum one because $1+\alpha/2&gt;1$, so a second application of Tonelli gives mass one for $\widetilde D_L$. The Riemann-sum limit $L^{-d}H_L^0\to\int h=1$ proves eventual positivity. It makes no assertion for an unchecked small value of $L$.</p>
<p>For the cube, $\widetilde U_L(x)=(2L+1)^{-d}\mathbf1_{\{\|x\|_\infty\leq L\}}$. Symmetry passes to convolution powers and their mixture. Each coordinate step $\pm e_i$ has positive mass in the $t=1$ term, so it is possible to reach every lattice point and the law is not concentrated at zero. The same term gives $\widetilde D_L(0)&gt;0$, proving period one. For the punctured cube, the coordinate steps still have positive mass, while</p>
<div class="math-display">$$D_L^*(0)\geq\frac{2^{-1-\alpha/2}}{\zeta(1+\alpha/2)}
\sum_x U_L^*(x)U_L^*(-x)&gt;0.$$</div>
<p>Thus the compound walk is aperiodic even when the punctured base walk is periodic, as it is at $d=L=1$.</p>
<p>The <a href="/errata/chen-sakai-marginal-2019/#compound-zeta-normalization">provisional erratum</a> retains DTYB's infinite-mass counterexample. The correction above proves normalization for every stated $h$ and the support properties for the cube; it does not establish the analytic hypotheses of the marginal percolation theorem. Those are the two-sided one-step bound (1.6), Fourier estimates (1.9)–(1.11), and heat-kernel bounds (1.12)–(1.13). The earlier Appendix A uses the all-lattice law but assumes $\alpha\ne2$. Its analysis therefore cannot by itself certify the marginal case. Section 2.2 of the later paper obtains (1.12) at $\alpha=2$ from Fourier inputs; verification of those inputs and the off-diagonal bound for the selected law is separate.</p>


## The fourth-moment correction for finite-range walks {#section-finite-range-correction}

<a id="tag-SPSG" data-assertion="theorem" data-title="A symmetric finite-range walk has a covariance-normalized fourth-moment Green correction"></a>
<p>Let $d\ge3$, and let $p$ be a symmetric probability mass function of finite support whose support generates $\mathbb Z^d$. Let $Z$ have law $p$, and put</p>
<div class="math-display">$$
\Sigma=\mathbb E[ZZ^{\mathsf T}],\qquad
B=\Sigma^{-1/2}Z,\qquad
r=(x^{\mathsf T}\Sigma^{-1}x)^{1/2},\qquad
\theta=\frac{\Sigma^{-1/2}x}{r}\quad(x\ne0).
$$</div>
<p>The positive definite square root is used. Define, for $|\theta|=1$,</p>
<div class="math-display">$$
P_p(\theta)=\mathbb E\!\left[
d(d+2)(B\cdot\theta)^4
-6d|B|^2(B\cdot\theta)^2+3|B|^4
\right],\qquad
c_d=\frac{\Gamma(d/2-1)}{2\pi^{d/2}}.
$$</div>
<p>Then the Green function has the expansion</p>
<div class="math-display">$$
G_p(x)=\frac{c_d}{\sqrt{\det\Sigma}}\left[
r^{2-d}+\frac{d-2}{24}\,r^{-d}P_p(\theta)
\right]+O_p(r^{-d-2}).
$$</div>
<p>The error is uniform in lattice direction for each fixed law $p$. Aperiodicity and an atom at zero are not required. If the normalized fourth moment is isotropic, in the precise sense</p>
<div class="math-display">$$
\mathbb E[(v\cdot B)^4]=\kappa|v|^4\qquad(v\in\mathbb R^d),
$$</div>
<p>then $P_p$ vanishes identically and the leading term alone has error $O_p(r^{-d-2})$.</p>
<p><em>Proof.</em> The generating assumption makes $\Sigma$ positive definite, as in 02EB. Since $p$ is symmetric, $\widehat p$ is real, and $q=1-\widehat p$ vanishes only at zero on the frequency torus: equality requires $k\cdot z\in2\pi\mathbb Z$ for every supported step. Moreover $q(k)\asymp|k|^2$ near zero. The same Abel-limit argument as in <a href="/tag/IY26/">IY26</a> therefore gives</p>
<div class="math-display">$$
G_p(x)=\int_{[-\pi,\pi]^d}\frac{e^{ik\cdot x}}{q(k)}\,\frac{dk}{(2\pi)^d}.
$$</div>
<p>In particular, a point where $\widehat p=-1$ causes no singularity. Only the neighbourhood of $q=0$ contributes to the power terms of the spatial expansion.</p>
<p>For that neighbourhood change variables to $\xi=\Sigma^{1/2}k$ and $y=\Sigma^{-1/2}x$. Finite support and symmetry give</p>
<div class="math-display">$$
q(\Sigma^{-1/2}\xi)
=\frac{|\xi|^2}{2}-\frac{\mathbb E[(\xi\cdot B)^4]}{24}
+O_p(|\xi|^6),
$$</div>
<p>and hence</p>
<div class="math-display">$$
\frac1{q(\Sigma^{-1/2}\xi)}
=\frac2{|\xi|^2}
+\frac16\frac{\mathbb E[(\xi\cdot B)^4]}{|\xi|^4}
+R_p(\xi),\qquad
|\partial^\alpha R_p(\xi)|\le C_{p,\alpha}|\xi|^{2-|\alpha|}.
$$</div>
<p>The derivative estimate follows by factoring out $|\xi|^2/2$ in polar coordinates and inverting the remaining smooth positive factor, exactly as in IY26. Choose a smooth cutoff supported in this neighbourhood, small enough that its image in $\xi$ lies in the unit ball. <a href="/tag/C5GY/">C5GY</a> bounds the inverse of the localized remainder by $O_p(|y|^{-d-2})$. The complementary torus symbol is smooth and periodic, so its coefficients decrease faster than every inverse power at integer $x$. The two norms $|y|$ and $|x|$ are comparable for the fixed law.</p>
<p>The inverse of $2|\xi|^{-2}$ is $c_d|y|^{2-d}$. For a fixed vector $b$, the fourth-order inverse away from zero is</p>
<div class="math-display">$$
\mathcal F^{-1}\!\left(\frac{(\xi\cdot b)^4}{|\xi|^4}\right)(y)
=\frac{\Gamma(d/2)}{4\pi^{d/2}}|y|^{-d}
\left[d(d+2)(b\cdot\theta)^4
-6d|b|^2(b\cdot\theta)^2+3|b|^4\right].
$$</div>
<p>Indeed, if $h_t(y)=(4\pi t)^{-d/2}e^{-|y|^2/(4t)}$, the inverse is $\int_0^\infty t(b\cdot\nabla)^4h_t(y)\,dt$. Differentiation gives</p>
<div class="math-display">$$
t(b\cdot\nabla)^4h_t(y)
=\left[\frac{(b\cdot y)^4}{16t^3}
-\frac{3|b|^2(b\cdot y)^2}{4t^2}
+\frac{3|b|^4}{4t}\right]h_t(y).
$$</div>
<p>Substitution of $u=|y|^2/(4t)$ proves the formula. The distributional identity and the off-origin time integral are justified as in IY26; the symbol is bounded by $|b|^4$, and the differentiated time integral converges locally away from zero. Thus the argument includes dimensions three and four.</p>
<p>Average over the finitely many values of $B$, multiply by $1/6$ and the Jacobian $(\det\Sigma)^{-1/2}$, and use $\Gamma(d/2)=(d-2)\Gamma(d/2-1)/2$. C5GY's cutoff comparison gives the claimed expansion. If the fourth moment is isotropic, the second homogeneous symbol is the constant $\kappa/6$. Its inverse is supported at the origin, so its cutoff inverse decreases faster than every inverse power. Equivalently, the displayed formula gives $P_p=0$. $\square$</p>
<p>The isotropy condition can hold for an irreducible finite-range law. For example, take independent coordinates which equal $-1,0,1$ with probabilities $1/6,2/3,1/6$. Their variance is $1/3$, and the normalized fourth moment is $\mathbb E[(v\cdot B)^4]=3|v|^4$. The result does not assert a nonzero correction for every step law.</p>
<p>Both terms have the correct holding normalization. If $p_a=(1-a)\delta_0+ap$, $0&lt;a\le1$, then $G_{p_a}=a^{-1}G_p$. Indeed $\Sigma_a=a\Sigma$, $r_a=a^{-1/2}r$ and $P_{p_a}=a^{-1}P_p$, so both displayed terms scale by $a^{-1}$. By <a href="/tag/94E7/">94E7</a>, the expansion also describes expected occupation for a critical branching walk with step law $p$; it is not a hitting-probability expansion.</p>

## The spread-out box correction {#section-box-green-correction}

<a id="tag-W810" data-assertion="corollary" data-title="The uniform box walk has an explicit angular Green correction with the opposite sign to nearest-neighbour walk"></a>
<p>Let $L\ge1$ and $d\ge3$ be integers, and let $D_L$ be uniform on $\{-L,\ldots,L\}^d$, including zero. Put $u=L(L+1)$, $\sigma_L^2=u/3$, $R=|x|$, and</p>
<div class="math-display">$$
Y_4(\theta)=\sum_i\theta_i^4-\frac3{d+2},\qquad
b_{d,L}=\frac{d(d-2)(d+2)(2u+1)}{120}.
$$</div>
<p>For the ordinary walk with this step law, uniformly in lattice direction as $R\to\infty$,</p>
<div class="math-display">$$
G_{D_L}(x)=\frac{c_d}{\sigma_L^2}
\left[R^{2-d}-b_{d,L}R^{-d}Y_4(x/R)\right]
+O_{d,L}(R^{-d-2}).
$$</div>
<p>The parameters $d,L$ are fixed in this asymptotic. For the law uniform on the nonzero points of the same box, multiply both displayed terms by $1-(2L+1)^{-d}$.</p>
<p><em>Proof.</em> The box law is symmetric and its support contains every coordinate step. Its coordinates are independent, with</p>
<div class="math-display">$$
\mathbb E Z_i^2=\frac u3,\qquad
\mathbb E Z_i^4=\frac{u(3u-1)}{15},\qquad
\mathbb E[Z_i^2Z_j^2]=\frac{u^2}{9}\quad(i\ne j).
$$</div>
<p>For $B=Z/\sigma_L$, define its marginal excess fourth moment</p>
<div class="math-display">$$
\eta_L=\mathbb E B_i^4-3=-\frac{3(2u+1)}{5u}&lt;0.
$$</div>
<p>Independence and vanishing odd moments give</p>
<div class="math-display">$$
\mathbb E[(v\cdot B)^4]=3|v|^4+\eta_L\sum_i v_i^4,\qquad
P_{D_L}(\theta)=d(d+2)\eta_LY_4(\theta).
$$</div>
<p>Apply SPSG with $\Sigma=\sigma_L^2 I$, $r=R/\sigma_L$, and the same unit direction $\theta=x/R$. The ratio of the correction coefficient to $c_d/\sigma_L^2$ is</p>
<div class="math-display">$$
\frac{d(d-2)(d+2)}{24}\,\sigma_L^2\eta_L=-b_{d,L},
$$</div>
<p>as asserted. Finally, $D_L=(2L+1)^{-d}\delta_0+[1-(2L+1)^{-d}]D_L^{\ne0}$, so the holding identity in SPSG gives $G_{D_L^{\ne0}}=[1-(2L+1)^{-d}]G_{D_L}$. $\square$</p>
<p>For $d=6$ and $L=1$, this reads</p>
<div class="math-display">$$
G_{D_1}(x)=\frac3{4\pi^3}
\left[R^{-4}+\left(3-8\sum_i(x_i/R)^4\right)R^{-6}\right]
+O(R^{-8}).
$$</div>
<p>The angular coefficient is $-5$ on a coordinate axis and $5/3$ on a body diagonal, the opposite signs to the nearest-neighbour correction. The leading amplitude is also different because the one-coordinate variance is $2/3$, rather than $1/6$. These formulas describe walk occupation. They do not give a percolation expansion or a remainder uniform as $L\to\infty$.</p>




## Killing at a logarithmic diagram boundary {#section-logarithmic-killing}

<p>The orders in <a href="/tag/KEPD/">KEPD</a> do not describe how a finite marginal diagram approaches its critical value. An exact leading symbol determines that rate, as well as the coefficient when the diagram diverges.</p>

<a id="tag-S4WN" data-assertion="theorem" data-title="Exact killing asymptotics at a logarithmically corrected diagram boundary"></a>
<p>Let $p$ be a symmetric probability mass function on $\mathbb Z^d$ whose support generates $\mathbb Z^d$. Suppose that, uniformly in direction,</p>
<div class="math-display">$$
q(k):=1-\widehat p(k)\sim v|k|^\alpha\bigl(\log(1/|k|)\bigr)^\beta
\qquad(k\to0),
$$</div>
<p>where $v&gt;0$, $0&lt;\alpha\le2$ and $\beta\in\mathbb R$. Fix an integer $s\ge1$ with $d=\alpha s$, and write</p>
<div class="math-display">$$
G_\lambda(x)=\sum_{n\ge0}\lambda^np^{*n}(x),\qquad
D_s(\lambda)=(G_\lambda^{*s})(0),\qquad
\gamma=\beta s,\qquad
A=\frac{|\mathbb S^{d-1}|}{(2\pi)^dv^s}.
$$</div>
<p>Set $\varepsilon=1-\lambda$ and $E=\log(1/\varepsilon)$. As $\lambda\uparrow1$,</p>
<div class="math-display">$$
\begin{aligned}
D_s(\lambda)&\sim\frac{A\alpha^{\gamma-1}}{1-\gamma}E^{1-\gamma}
&& (\gamma&lt;1),\\
D_s(\lambda)&\sim A\log E
&& (\gamma=1),\\
D_s(1)-D_s(\lambda)&\sim
\frac{A\alpha^{\gamma-1}}{\gamma-1}E^{1-\gamma}
&& (\gamma&gt;1).
\end{aligned}
$$</div>
<p>Here $D_s(1)$ is finite exactly when $\gamma&gt;1$. All limits concern a fixed step law. No holding assumption is needed.</p>
<p><em>Proof.</em> Since $p$ is symmetric, $q=\sum_xp(x)(1-\cos(k\cdot x))\ge0$. Its only zero on the torus is the origin: vanishing forces $k\cdot x\in2\pi\mathbb Z$ for every point of the support, which generates the lattice. Thus $q$ is bounded below off any neighbourhood of zero.</p>
<p>For $\lambda&lt;1$, the Green function is summable. Fourier inversion and convolution give, with normalized torus measure,</p>
<div class="math-display">$$
D_s(\lambda)=\lambda^{-s}J_s(t),\qquad
J_s(t)=\int(t+q(k))^{-s}\,\frac{dk}{(2\pi)^d},\qquad
t=\frac{1-\lambda}{\lambda}.
$$</div>
<p>Monotone convergence applies to the nonnegative spatial sums. On the Fourier side it applies on $\{\widehat p\ge0\}$, while the integrands on $\{\widehat p&lt;0\}$ are bounded by one and converge by dominated convergence. Consequently $D_s(1)=\int q^{-s}$, with infinity allowed. The hypothesis reduces finiteness near zero to that of $\int^\infty u^{-\gamma}\,du$.</p>
<p>First replace $q$ on a small ball by $w(r)=vr^\alpha(\log(1/r))^\beta$. Choose its radius $\delta$ so that $w$ is increasing there. Let $\rho_t&lt;\delta$ solve $w(\rho_t)=t$, and put $U_t=\log(1/\rho_t)$ and $U_0=\log(1/\delta)$. Taking logarithms gives</p>
<div class="math-display">$$
\alpha U_t=\log(1/t)+\beta\log U_t+\log v,
\qquad U_t\sim\alpha^{-1}\log(1/t).
$$</div>
<p>The contribution of $r&lt;\rho_t$ to the damped integral is $O(t^{-s}\rho_t^d)=O(U_t^{-\gamma})$. On $\rho_t&lt;r&lt;\delta$, replacing $(t+w)^{-s}$ by $w^{-s}$ incurs an error at most</p>
<div class="math-display">$$
C t\int_{\rho_t}^{\delta}
r^{-\alpha-1}(\log(1/r))^{-\beta(s+1)}\,dr
=O(U_t^{-\gamma}).
$$</div>
<p>For the last estimate substitute $u=\log(1/r)$: the integral is bounded by a constant times $e^{\alpha U_t}U_t^{-\beta(s+1)}$. This bound follows by differentiating $e^{\alpha u}u^{-\beta(s+1)}$ for large $u$; the initial bounded interval contributes $O(t)$.</p>
<p>When $\gamma\le1$, the model integral is therefore</p>
<div class="math-display">$$
A\int_{U_0}^{U_t}u^{-\gamma}\,du+O(U_t^{-\gamma}).
$$</div>
<p>When $\gamma&gt;1$, apply the same estimates to its deficit from the critical integral. The contribution below $\rho_t$ is the critical tail minus an $O(U_t^{-\gamma})$ damped term, while the contribution above $\rho_t$ is $O(U_t^{-\gamma})$. Thus the deficit is</p>
<div class="math-display">$$
A\int_{U_t}^{\infty}u^{-\gamma}\,du+O(U_t^{-\gamma}).
$$</div>
<p>Evaluation of these integrals gives the displayed constants for the model.</p>
<p>To pass to $q$, fix $0&lt;\eta&lt;1$ and shrink $\delta$ until $(1-\eta)w\le q\le(1+\eta)w$. The divergent integrals are squeezed between the corresponding model integrals; their bounded complements do not affect the equivalents. For the finite case use</p>
<div class="math-display">$$
g_t(a)=a^{-s}-(t+a)^{-s}.
$$</div>
<p>This function is positive and decreasing in $a$, and $g_t(cw)=c^{-s}g_{t/c}(w)$. The same squeeze therefore applies to the deficit, whose complement is $O(t)$. Letting $\eta\downarrow0$ proves the equivalents for $J_s$. Finally $\log(1/t)\sim E$ and $\lambda^{-s}=1+O(\varepsilon)$. In the finite case the additional term from this factor is $O(\varepsilon)$, negligible compared with $E^{1-\gamma}$. This proves the result. $\square$</p>
<p>The assumption $q\sim w$ alone gives equivalents, not a bounded remainder or a finite constant after subtracting a divergence. For the concrete marginal walk, <a href="/tag/V7FQ/">V7FQ</a> gives the stronger error needed below.</p>

## Exact marginal deficits and a double-logarithmic finite part {#section-marginal-killing-expansion}

<a id="tag-Q7D7" data-assertion="theorem" data-title="The clipped marginal walk has explicit diagram deficits and a two-dimensional finite part"></a>
<p>Take the clipped power-law step distribution $D_L$ from <a href="/articles/branching-random-walk/#section-marginal-step-law">the marginal step-law section</a>, with fixed $L\ge1$. Use $G_\lambda$, $D_s(\lambda)$ and $E=\log(1/(1-\lambda))$ as above, now with $p=D_L$. In dimension $d=2s$ write $v=v_L=|\mathbb S^{d-1}|/(2dZ_L)$.</p>
<p>If $s\ge2$, then $D_s(1)&lt;\infty$ and</p>
<div class="math-display">$$
D_s(1)-D_s(\lambda)
=K_s E^{1-s}-K_s(s-1)E^{-s}\log E+O_L(E^{-s}),
\qquad
K_s=\frac1{(2\pi)^s\Gamma(s)(s-1)v^s}.
$$</div>
<p>In particular, the bubble in dimension four and the triangle in dimension six satisfy</p>
<div class="math-display">$$
\begin{aligned}
D_2(1)-D_2(\lambda)
&=\frac1{4\pi^2v^2}
\left[\frac1E-\frac{\log E}{E^2}+O_L(E^{-2})\right],\\
D_3(1)-D_3(\lambda)
&=\frac1{32\pi^3v^3}
\left[\frac1{E^2}-\frac{2\log E}{E^3}+O_L(E^{-3})\right].
\end{aligned}
$$</div>
<p>Each $v$ is computed in the dimension of its formula. In dimension two there is a finite constant $b_L$ such that</p>
<div class="math-display">$$
G_\lambda(0)=\frac1{2\pi v}\left[\log E+\frac{\log E}{E}\right]
+b_L+O_L(E^{-1}).
$$</div>
<p>For any sufficiently small $\delta&lt;e^{-1}$ this constant is</p>
<div class="math-display">$$
b_L=\int_{[-\pi,\pi]^2}
\left[\frac1{q(k)}-
\frac{\mathbf1_{\{|k|&lt;\delta\}}}{v|k|^2\log(1/|k|)}\right]
\frac{dk}{(2\pi)^2}
-\frac1{2\pi v}\log\bigl(2\log(1/\delta)\bigr).
$$</div>
<p>The bracket is integrated as one function; the two terms separately have divergent integrals. All errors are for fixed $d$ and $L$.</p>
<p><em>Proof.</em> By V7FQ, uniformly near zero,</p>
<div class="math-display">$$
q(k)=w(|k|)\left(1+O_L\bigl(1/\log(1/|k|)\bigr)\right),
\qquad w(r)=vr^2\log(1/r).
$$</div>
<p>Use the cutoff $\rho_t$ and $U_t$ in S4WN. For $u=\log(1/r)$, differentiation of $g_t$ gives</p>
<div class="math-display">$$
|g_t(q(k))-g_t(w(r))|
\le\frac{C_L}{u}\min\{w(r)^{-s},\ t w(r)^{-s-1}\}.
$$</div>
<p>Indeed $q$ and $w$ are comparable, $|q-w|\le C_Lw/u$, and $|g_t'(a)|\le C_s\min\{a^{-s-1},t a^{-s-2}\}$ between them. In dimension $2s$, integration below $\rho_t$ is bounded by $C_L\int_{U_t}^\infty u^{-s-1}du=O_L(U_t^{-s})$. Above $\rho_t$, the second term and the exponential estimate used in S4WN give $O_L(U_t^{-s-1})$. The complement of the ball contributes $O_L(t)$.</p>
<p>For $s\ge2$, the model deficit and this comparison yield</p>
<div class="math-display">$$
D_s(1)-D_s(\lambda)
=\frac{A}{s-1}U_t^{1-s}+O_L(U_t^{-s}),
\qquad A=\frac{|\mathbb S^{2s-1}|}{(2\pi)^{2s}v^s}.
$$</div>
<p>The factor $\lambda^{-s}$ changes the deficit by only $O_L(\varepsilon)$. Solving $2U_t=\log(1/t)+\log U_t+\log v$ one step further gives</p>
<div class="math-display">$$
U_t=\frac12\left[E+\log E+\log(v/2)
+O_L\left(\frac{\log E}{E}\right)\right].
$$</div>
<p>Expanding $U_t^{1-s}$ and using $|\mathbb S^{2s-1}|=2\pi^s/\Gamma(s)$ proves the formula for $K_s$ and its next logarithmic term.</p>
<p>For $s=1$, let $R(t)$ be $J_1(t)$ minus the damped model integral over $|k|&lt;\delta$. The pointwise difference $q^{-1}-w^{-1}$ is $O_L(r^{-2}u^{-2})$, which is integrable in two dimensions. Hence $R(0)$ is the bracketed integral in the statement. The same bound on $g_t(q)-g_t(w)$ proves $R(t)-R(0)=O_L(U_t^{-1})$. The model calculation gives</p>
<div class="math-display">$$
J_1(t)=A\log U_t-A\log U_0+R(0)+O_L(U_t^{-1}),
\qquad A=\frac1{2\pi v},\quad U_0=\log(1/\delta).
$$</div>
<p>The expansion of $U_t$ implies $\log U_t=\log E-\log2+(\log E)/E+O_L(E^{-1})$. Multiplication by $\lambda^{-1}$ has a smaller effect. This proves the asserted expansion and the expression for $b_L$. Changing $\delta$ changes $R(0)$ by the integral of $w^{-1}$ over the intervening annulus, exactly cancelling the change in $-A\log U_0$; thus $b_L$ is independent of the cutoff. $\square$</p>
<p>The positive deficit decays only as $1/\log(1/\varepsilon)$ for the four-dimensional bubble and as $1/(\log(1/\varepsilon))^2$ for the six-dimensional triangle. Their finiteness differs from the finite-range marginal logarithms in <a href="/tag/KC8U/">KC8U</a>. These expansions use the walk's symbol and do not infer a near-critical percolation expansion from the critical comparison in 6ZYT.</p>




## The spatial profile with killing {#section-marginal-spatial-crossover}

<p>Retain the clipped marginal law $D_L$, with $L$ fixed, and put</p>
<div class="math-display">$$
H_{j,\lambda}(x)=G_\lambda^{*j}(x),\qquad
N_R=\frac{R^2}{v_L\log R},\qquad R=|x|&gt;1.
$$</div>
<p>Here $j\ge1$ is an integer, and all limits below are for fixed $d$, $j$ and $L$. The time $N_R$ is the scale on which the walk reaches distance $R$; killing on that scale produces the following profile.</p>

<a id="tag-C9HG" data-assertion="theorem" data-title="Marginal long-range Green potentials have a uniform near-critical spatial profile"></a>
<p>For $\theta&gt;0$ define</p>
<div class="math-display">$$
\Psi_{d,j}(\theta)=\frac1{\Gamma(j)(4\pi)^{d/2}}
\int_0^\infty t^{j-1-d/2}
\exp\!\left(-\frac1{4t}-\theta t\right)dt.
$$</div>
<p>In every dimension $d\ge1$, uniformly in lattice direction and for $\theta$ in each compact subset of $(0,\infty)$,</p>
<div class="math-display">$$
\frac{R^d}{N_R^j}H_{j,\exp(-\theta/N_R)}(x)
\longrightarrow\Psi_{d,j}(\theta)
\qquad(R\to\infty).
$$</div>
<p>If $d&gt;2j$, this convergence is uniform also for $0\le\theta\le M$, for every finite $M$, with</p>
<div class="math-display">$$
\Psi_{d,j}(0)=\frac{\Gamma(d/2-j)}{4^j\pi^{d/2}\Gamma(j)}.
$$</div>
<p>At $d=2j$ and $\theta&gt;0$, the profile is</p>
<div class="math-display">$$
\Psi_{2j,j}(\theta)=\frac{2K_0(\sqrt\theta)}{(4\pi)^j\Gamma(j)},
\qquad
K_0(z)=\frac12\int_0^\infty
\exp\!\left[-\frac z2(u+u^{-1})\right]\frac{du}{u}.
$$</div>
<p>In particular $\Psi_{2j,j}(\theta)\sim[(4\pi)^j\Gamma(j)]^{-1}\log(1/\theta)$ as $\theta\downarrow0$. No uniform approximation down to $\theta=0$ is asserted at or below $d=2j$.</p>
<p><em>Proof.</em> Markov composition and Tonelli, as in <a href="/tag/CEVT/">CEVT</a>, give the exact identity</p>
<div class="math-display">$$
H_{j,\lambda}(x)=\sum_{n\ge0}\binom{n+j-1}{j-1}\lambda^nD_L^{*n}(x).
$$</div>
<p>For $0&lt;a&lt;b&lt;\infty$, <a href="/tag/V7FQ/">V7FQ</a> gives, uniformly for $a\le n/N_R\le b$ and in the direction of $x$,</p>
<div class="math-display">$$
R^dD_L^{*n}(x)
-(4\pi n/N_R)^{-d/2}\exp\!\left(-\frac1{4n/N_R}\right)
\longrightarrow0.
$$</div>
<p>Indeed $n\log n/R^2\to2t/v_L$ when $n/N_R\to t$. The binomial coefficient is uniformly asymptotic to $n^{j-1}/\Gamma(j)$ on this interval, and $\lambda^n=e^{-\theta n/N_R}$. A Riemann sum therefore gives the integral defining $\Psi_{d,j}$ over $[a,b]$, uniformly for $\theta$ in a fixed bounded interval.</p>
<p>The omitted early times are controlled by the transition estimate <a href="/tag/G12U/">G12U</a>. Since $x\ne0$, generation zero contributes nothing, and</p>
<div class="math-display">$$
\limsup_{R\to\infty}\frac{R^d}{N_R^j}
\sum_{1\le n&lt;aN_R}\binom{n+j-1}{j-1}
\lambda^nD_L^{*n}(x)\le C_La^{j+1}.
$$</div>
<p>To obtain this bound, use $\lambda^n\le1$, sum $C_Ln^j\log R/R^{d+2}$, and substitute $N_R\log R/R^2=1/v_L$. For late times, V7FQ gives $D_L^{*n}(x)\le C_L(n\log n)^{-d/2}$. If $\theta\ge\theta_0&gt;0$, then for $b\ge1$ the scaled tail has limit superior at most</p>
<div class="math-display">$$
C_L\int_b^\infty t^{j-1-d/2}e^{-\theta_0t}\,dt.
$$</div>
<p>Here $\log n\ge\log(bN_R)\sim2\log R$, and comparison of the remaining sum with a time integral is uniform in $\theta$. The bound tends to zero as $b\to\infty$. When $d&gt;2j$, the same argument works with $\theta_0=0$, giving $C_Lb^{j-d/2}$. Letting $a\downarrow0$ and $b\uparrow\infty$ proves both uniform limits. The integral at $\theta=0$ is evaluated by $u=1/(4t)$.</p>
<p>At $d=2j$, substitute $t=u/(2\sqrt\theta)$ to obtain the formula with $K_0$. For its small-$\theta$ equivalent, split the original integral at $t=1$ and $t=1/\theta$. The two tails are bounded uniformly. On the middle interval, replacing $e^{-1/(4t)-\theta t}$ by one changes the integral by at most</p>
<div class="math-display">$$
\int_1^{1/\theta}\left(\frac1{4t^2}+\theta\right)dt=O(1).
$$</div>
<p>Thus that integral is $\log(1/\theta)+O(1)$, proving the last assertion. $\square$</p>
<p>Equivalently, the killing parameter on this scale is $(1-\lambda)R^2/(v_L\log R)\sim\theta$. The uniformity just proved is on compact sets of this parameter. It does not give a relative asymptotic when killing is fixed and the distance tends to infinity.</p>

## The fraction of a critical marginal potential that survives {#section-marginal-surviving-fraction}

<p>When $d=2j$ and $j\ge2$, the critical potential $H_j=H_{j,1}$ is finite. Its leading contribution comes from times much later than $N_R$, so a different limit describes a nonzero fraction of it.</p>

<a id="tag-4XHU" data-assertion="theorem" data-title="A logarithmic time ratio determines uniformly how much of a critical marginal Green potential survives killing"></a>
<p>Suppose $d=2j$ with $j\ge2$, and define</p>
<div class="math-display">$$
E_\lambda=\log\frac1{1-\lambda}\quad(0\le\lambda&lt;1),\qquad E_1=\infty,
\qquad
F_j(u)=
\begin{cases}
0,&0\le u\le1,\\
1-u^{1-j},&1&lt;u&lt;\infty,\\
1,&u=\infty.
\end{cases}
$$</div>
<p>Then, uniformly in lattice direction,</p>
<div class="math-display">$$
\sup_{0\le\lambda\le1}
\left|\frac{H_{j,\lambda}(x)}{H_j(x)}
-F_j\!\left(\frac{E_\lambda}{2\log|x|}\right)\right|
\longrightarrow0
\qquad(|x|\to\infty).
$$</div>
<p>For example, if $\lambda=1-|x|^{-\kappa}$ with fixed $\kappa&gt;0$, the surviving fraction tends to zero for $\kappa\le2$, and to $1-(2/\kappa)^{j-1}$ for $\kappa&gt;2$. At $\kappa=4$ this is one half for the four-dimensional bubble potential and three quarters for the six-dimensional triangle potential.</p>
<p><em>Proof.</em> Put $R=|x|$, $M=\lceil R^2\rceil$, and $a_j=(2\pi v_L)^{-j}/\Gamma(j)$. The early-time estimates in CEVT give, uniformly in $\lambda\in[0,1]$,</p>
<div class="math-display">$$
\sum_{n&lt;M}\binom{n+j-1}{j-1}\lambda^nD_L^{*n}(x)
=O_L\!\left(\frac{\log\log R}{(\log R)^j}\right)
=o((\log R)^{1-j}).
$$</div>
<p>Specifically, below $R^2/\log R$ use G12U; between that time and $R^2$ use V7FQ. Both bounds remain valid after discounting. For all $n\ge M$, one has $|x|/\sqrt{n\log n}\le(2\log R)^{-1/2}$. The uniform local limit in V7FQ and the binomial asymptotic therefore give</p>
<div class="math-display">$$
\binom{n+j-1}{j-1}D_L^{*n}(x)
=\frac{a_j+o(1)}{n(\log n)^j},
$$</div>
<p>where the error is uniform over this whole time range and in direction. Since $\sum_{n\ge M}[n(\log n)^j]^{-1}=O((\log R)^{1-j})$, it follows that</p>
<div class="math-display">$$
H_{j,\lambda}(x)
=a_j\sum_{n\ge M}\frac{\lambda^n}{n(\log n)^j}
+o((\log R)^{1-j})
$$</div>
<p>uniformly in $\lambda$.</p>
<p>For $\lambda&lt;1$, set $\varepsilon=1-\lambda$ and $N=\varepsilon^{-1}$. Replacing $\lambda^n$ in this sum by $\mathbf1_{\{n\le N\}}$ costs $O((\log M)^{-j})$, uniformly in $\lambda$. If $N\ge M$, the error below $N$ is bounded using $1-\lambda^n\le n\varepsilon$:</p>
<div class="math-display">$$
\sum_{M\le n\le N}\frac{1-\lambda^n}{n(\log n)^j}
\le\varepsilon\sum_{M\le n\le N}(\log n)^{-j}
\le(\log M)^{-j}.
$$</div>
<p>The tail above $N$ is bounded by $(\log M)^{-j}\sum_{n&gt;N}e^{-n/N}/n=O((\log M)^{-j})$. If $N&lt;M$, the same exponential bound applies to the entire sum, since $M/N&gt;1$. At $\lambda=1$ take $N=\infty$, with no replacement error.</p>
<p>The integral test, uniformly in the upper endpoint, now gives</p>
<div class="math-display">$$
H_{j,\lambda}(x)
=\frac{a_j}{j-1}
\left[(\log M)^{1-j}-\max\{\log M,E_\lambda\}^{1-j}\right]
+o((\log R)^{1-j}),
$$</div>
<p>where $\infty^{1-j}=0$. The sum-to-integral error is at most a constant times $[M(\log M)^j]^{-1}$. Since $\log M\sim2\log R$, and CEVT gives $H_j(x)\sim a_j(2\log R)^{1-j}/(j-1)$, division proves the claimed uniform limit. Replacing $\log M$ by $2\log R$ is uniform in $E_\lambda$: the maximum is nondecreasing and its relative change is bounded by that of these two lower cutoffs. $\square$</p>
<p>For $\lambda=\exp(-\theta/N_R)$ with $\theta$ in a compact subset of $(0,\infty)$, C9HG and CEVT give the more precise comparison</p>
<div class="math-display">$$
\frac{H_{j,\lambda}(x)}{H_j(x)}
\sim\frac{(j-1)K_0(\sqrt\theta)}{\log R},
$$</div>
<p>uniformly on that compact set. Thus the spatial crossover profile captures a vanishing fraction of the critical potential. A positive limiting fraction requires the longer killing times quantified by $F_j$. These are walk potentials; the critical percolation comparison in 6ZYT does not supply the near-critical estimates needed to transfer either statement to percolation.</p>




## Perturbing every convolution factor {#section-convolution-amplitude-transfer}

<p>The spatial equivalent in 6ZYT contains more information than the comparison used there. To pass its leading coefficient through a convolution, we must check that changing the kernel on a bounded set has a negligible effect.</p>

<a id="tag-B3YC" data-assertion="theorem" data-title="Asymptotically proportional kernels transfer convolution amplitudes when bounded displacements are negligible"></a>
<p>Let $G:\mathbb Z^d\to(0,\infty)$, fix an integer $j\ge2$, and write $H_m=G^{*m}$ for its nonnegative convolution powers. Suppose $H_j(x)&lt;\infty$ for every $x$ and, for each fixed $z\in\mathbb Z^d$,</p>
<div class="math-display">$$
\frac{H_{j-1}(x-z)}{H_j(x)}\longrightarrow0
\qquad(|x|\to\infty).
$$</div>
<p>If $f_1,\ldots,f_j:\mathbb Z^d\to\mathbb R$ are finite-valued and $f_i(x)/G(x)\to a_i\in\mathbb R$, then their convolution is absolutely convergent at every point and</p>
<div class="math-display">$$
\frac{(f_1*\cdots*f_j)(x)}{H_j(x)}
\longrightarrow\prod_{i=1}^j a_i.
$$</div>
<p>Signs and zero limiting coefficients are allowed. Every spatial limit here includes all lattice directions.</p>
<p><em>Proof.</em> Positivity of $G$ and the assumed limits give a finite constant $M\ge1$ such that $|f_i|\le MG$ and $|a_i|\le M$ for all $i$. Hence the absolute convolution is at most $M^jH_j$. Also $H_{j-1}(y)\le H_j(y)/G(0)&lt;\infty$, so the lower convolution order is well defined and finite.</p>
<p>Put $h_i=f_i-a_iG$. For each $\eta&gt;0$ there are a finite set $F$ and a finite constant $C_\eta$ such that, simultaneously for all $i$,</p>
<div class="math-display">$$
|h_i(y)|\le\eta G(y)+C_\eta\mathbf1_F(y).
$$</div>
<p>Replace the factors in the convolution one at a time. Absolute convergence justifies the resulting telescoping sum, and all its other factors are bounded by $MG$. Thus</p>
<div class="math-display">$$
\left|(f_1*\cdots*f_j)(x)-\left(\prod_i a_i\right)H_j(x)\right|
\le jM^{j-1}\left[\eta H_j(x)
+C_\eta\sum_{z\in F}H_{j-1}(x-z)\right].
$$</div>
<p>Divide by the positive quantity $H_j(x)$, let $|x|\to\infty$, and then let $\eta\downarrow0$. The sum over $F$ vanishes by the hypothesis. $\square$</p>
<p>For the clipped marginal walk, the hypothesis holds whenever its $j$th critical potential is finite. Indeed, let $G=G_L$, keep $d,j,L$ fixed, and suppose $d&gt;2j$ or $d=2j$ with $j\ge2$. By <a href="/tag/CEVT/">CEVT</a>, for each fixed $z$,</p>
<div class="math-display">$$
\frac{H_{j-1}(x-z)}{H_j(x)}
=\begin{cases}
O_{d,j,L,z}(|x|^{-2}\log|x|),&d&gt;2j,\\
O_{d,j,L,z}(|x|^{-2}),&d=2j.
\end{cases}
$$</div>
<p>Here $H_{j-1}$ is in the strict range $d&gt;2(j-1)$ in both cases. The estimates follow by dividing its equivalent by that of $H_j$, using $|x-z|/|x|\to1$ and $\log|x-z|/\log|x|\to1$. They are uniform in direction and for $z$ in any fixed finite set. Consequently, whenever $f_i/G_L\to a_i$, the limiting convolution coefficient is the product of the $a_i$, including at the logarithmic boundary.</p>

## Exact critical percolation potential amplitudes {#section-marginal-percolation-amplitudes}

<a id="tag-5DQV" data-assertion="corollary" data-title="The marginal long-range percolation two-point equivalent determines exact bubble and triangle potential amplitudes"></a>
<p>Consider the model of <a href="/tag/6ZYT/">6ZYT</a>: in $\mathbb Z^d$, each unordered bond $\{x,y\}$ is open independently with probability $pD_L(y-x)$, where $D_L$ is the clipped marginal power-law kernel. Let $d\ge6$ and take $L$ sufficiently large for the cited Chen–Sakai critical two-point equivalent to hold. Write $\tau=\tau_{p_c}$, $v=v_L$ and $R=|x|$. For every integer $j\ge1$ with $d&gt;2j$,</p>
<div class="math-display">$$
\tau^{*j}(x)\sim
\frac{\Gamma(d/2-j)}{4^j\pi^{d/2}\Gamma(j)(p_cv)^j}
\frac{R^{2j-d}}{(\log R)^j}.
$$</div>
<p>At $d=2j$ with $j\ge2$,</p>
<div class="math-display">$$
\tau^{*j}(x)\sim
\frac{2^{1-2j}}{\pi^j(p_cv)^j(j-1)\Gamma(j)}
(\log R)^{1-j}.
$$</div>
<p>These convolution sums are finite at every $x$, and the equivalents are uniform in direction for each fixed model. All higher orders, with $d&lt;2j$, are infinite at every $x$.</p>
<p>In dimension six, define the bubble and triangle potentials by</p>
<div class="math-display">$$
B(x)=\sum_y\tau(y)\tau(x-y),\qquad
T(x)=\sum_{y,z}\tau(y)\tau(z-y)\tau(x-z).
$$</div>
<p>Then</p>
<div class="math-display">$$
B(x)\sim\frac1{16\pi^3(p_cv)^2}\frac1{R^2(\log R)^2},
\qquad
T(x)\sim\frac1{128\pi^3(p_cv)^3}\frac1{(\log R)^2}.
$$</div>
<p><em>Proof.</em> The cited percolation equivalent in 6ZYT and the walk equivalent in CEVT imply $\tau(x)/G_L(x)\to p_c^{-1}$. For $j\ge2$ in the finite range, apply B3YC with every $f_i=\tau$ to obtain</p>
<div class="math-display">$$
\tau^{*j}(x)\sim p_c^{-j}H_j(x).
$$</div>
<p>The constants now follow from CEVT; for $j=1$ the formula is the cited two-point equivalent itself. The global comparison in 6ZYT gives finiteness or divergence at every point, including outside the finite range. Substituting $d=6$, $j=2$ and $j=3$ gives the two displayed amplitudes. $\square$</p>
<p>These are spatial equivalents as $R\to\infty$, not evaluations of $B(0)$ or $T(0)$. The coefficient $p_c$ is the multiplier in the bond probability $pD_L(y-x)$. The result concerns this sufficiently spread-out marginal long-range model; it supplies neither a nearest-neighbour dimension-six equivalent nor a reverse-BK inequality.</p>
