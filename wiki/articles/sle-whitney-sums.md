---
{
  "id": "sle-whitney-sums",
  "title": "Whitney sums for SLE hull boundaries",
  "subtitle": "The global moment threshold and an expected covering lower bound",
  "kind": "method",
  "category": "General theory",
  "summary": "A bound on the driving function localizes the preimages of the relevant Whitney squares. Its Gaussian tail makes the upper derivative moments summable globally. Small derivative scales transfer the critical divergence to Whitney sums, which then give an expected covering lower bound.",
  "context": [
    "We work at time one for ordinary chordal SLE. The probabilistic conclusions exclude kappa four, as does the source Whitney-sum theorem; they include kappa eight without a trace-construction input.",
    "The derivative moment estimates and the exact threshold for expected localized grids have already been proved. The remaining ingredients are Whitney squares, Koebe distortion, hyperbolic packing and the Brownian maximum tail.",
    "The divergence statements concern expectations. They do not imply almost-sure divergence of Whitney sums or a Hausdorff lower bound.",
    "The expected-covering argument uses a positive height buffer. Squares reaching height twice h are compared with the hull boundary above height h."
  ],
  "related": ["sle-hull-boundary", "sle-derivative-lower-bounds", "sle-derivative-estimates", "sle-trace-covering"],
  "sourceIds": ["rohde-schramm-basic-sle-2005"],
  "aliases": ["SLE Whitney decomposition", "SLE expected boundary covering", "SLE Whitney moment threshold"],
  "prototypeUses": []
}
---

## From Whitney squares to the inverse-map grid {#section-whitney-grid}

<p>Let $U:[0,1]\to\mathbb R$ be a continuous chordal Loewner driver with $U_0=0$. Write $D=D_1$, $K=\overline{\mathbb H\setminus D}$ and $F(z)=g_1^{-1}(z+U_1)$, and put $M=\sup_{0\leq t\leq1}|U_t|$. Take the maximal dyadic closed squares $Q\subset D$ satisfying $d(Q)\leq\operatorname{dist}(Q,\partial D)$, where $d(Q)$ is the side length. They cover $D$, have disjoint interiors, and satisfy</p>
<div class="math-display">$$d(Q)\leq\operatorname{dist}(Q,\partial D)\leq8d(Q).$$</div>
<p>Indeed, sufficiently small dyadic squares around an interior point satisfy the first inequality, whereas the parent of a maximal square fails it; comparing the square with its parent gives the upper bound. We use this fixed dyadic construction so that the sums below are measurable functions of the Loewner hull.</p>
<p>For $h,p&gt;0$, set</p>
<div class="math-display">$$\mathcal W_h=\{Q:\operatorname{dist}(Q,K)\leq1,\ \sup_{z\in Q}\operatorname{Im}z\geq h\},
\qquad S_h(p)=\sum_{Q\in\mathcal W_h}d(Q)^p.$$</div>
<p>Use $y_n=2^{-n}$ and $z_{j,n}=j y_n+i y_n$, $n\geq-2$, and write $A_{j,n}=y_n|F'(z_{j,n})|$. As in the <a href="/articles/sle-hull-boundary/#section-grid-sums">localized grid definition</a>,</p>
<div class="math-display">$$J_{p,h,L}(F)=\sum_{n\geq-2}\ \sum_{|j y_n|\leq L}
\mathbf1_{\{\operatorname{Im}F(z_{j,n})\geq h\}}A_{j,n}^p.$$</div>

<a id="tag-IDL1" data-assertion="proposition" data-title="Whitney sums near a time-one Loewner hull are bounded by inverse-map grid sums in a window controlled by the driver"></a>
<p>For every $p&gt;0$ there is a constant $C_p$, independent of the driver and of $h$, such that</p>
<div class="math-display">$$S_h(p)\leq C_p J_{p,h',\,2M+8}(F),
\qquad h'=\tfrac12e^{-2}h.$$</div>
<p><em>Proof.</em> The hull lies in $[-M,M]+i[0,2]$. For the horizontal bound, a point initially to the right of $M$ has an increasing real flow coordinate and stays a positive distance from every driving value; its imaginary part remains positive up to time one. The argument on the left is the same. The height bound follows from $\partial_t(\operatorname{Im}g_t(z))^2\geq-4$.</p>
<p>If $Q\in\mathcal W_h$, then $d(Q)\leq1$, since $\operatorname{dist}(Q,\partial D)\leq\operatorname{dist}(Q,K)$. Its centre $w$ therefore satisfies</p>
<div class="math-display">$$|\operatorname{Re}w|\leq M+3,\qquad h/2\leq\operatorname{Im}w\leq5.$$</div>
<p>Write $g_1(w)-U_1=x+iv$. The imaginary coordinate decreases under forward flow, so $0&lt;v\leq5$. If $X_t=\operatorname{Re}g_t(w)$, its equation gives, almost everywhere in time,</p>
<div class="math-display">$$\frac{d}{dt}(X_t-M)_+^2\leq4,
\qquad \frac{d}{dt}(-M-X_t)_+^2\leq4.$$</div>
<p>Thus $|X_1|\leq M+\sqrt{13}&lt;M+4$, and $|x|\leq2M+4$.</p>
<p>Choose a dyadic height $y_n\in[v/2,v]$ and a grid coordinate with $|j y_n-x|\leq y_n/2$. Then $n\geq-2$, $|j y_n|\leq2M+8$, and the hyperbolic distance in $\mathbb H$ from $z_{j,n}$ to $x+iv$ is at most two. Since $F$ is a hyperbolic isometry onto $D$, while inclusion of $D$ in $\mathbb H$ decreases hyperbolic distance,</p>
<div class="math-display">$$\operatorname{Im}F(z_{j,n})\geq e^{-2}\operatorname{Im}w\geq h'.$$</div>
<p>Koebe's quarter theorem says that the conformal radius $2v|F'(x+iv)|$ lies between $\operatorname{dist}(w,\partial D)$ and four times that distance. The Whitney inequalities and Koebe distortion over the bounded hyperbolic distance consequently give</p>
<div class="math-display">$$c\,d(Q)\leq A_{j,n}\leq C\,d(Q)$$</div>
<p>with absolute positive constants.</p>
<p>It remains to bound the number of squares assigned to one grid point. The hyperbolic density in $D$ lies between $1/(2\operatorname{dist}(z,\partial D))$ and $2/\operatorname{dist}(z,\partial D)$. On a Whitney square, the distance to the boundary lies between $d(Q)$ and $10d(Q)$. Each square therefore has hyperbolic diameter at most $2\sqrt2$ and hyperbolic area at least $1/400$. All squares assigned to one grid point lie in a hyperbolic ball of fixed radius around its image. Their interiors are disjoint, so hyperbolic area bounds their number by an absolute constant. Summing the derivative comparison proves the proposition.</p>

## A random window with a Gaussian tail {#section-random-window}

<p>Now take $U_t=\sqrt\kappa B_t$. For $\kappa&gt;0$ put</p>
<div class="math-display">$$\delta(\kappa)=
\begin{cases}1+\kappa/8,&\kappa\leq4,\\
1+2/\kappa,&\kappa\geq4.
\end{cases}$$</div>

<a id="tag-HQI8" data-assertion="proposition" data-title="The Brownian driving maximum preserves finite expected grid moments above the boundary exponent"></a>
<p>If $\kappa\ne4$, then for every $p&gt;\delta(\kappa)$ and $h&gt;0$,</p>
<div class="math-display">$$\mathbb E[J_{p,h,\,2M+8}(F)]&lt;\infty.$$</div>
<p><em>Proof.</em> We may decrease $h$ to at most one. Choose $b$ strictly between $\min\{1/2,2/\kappa\}$ and $\max\{1/2,2/\kappa\}$, close enough to the smaller endpoint that</p>
<div class="math-display">$$\delta(\kappa)&lt;a:=2b+\frac{\kappa b(1-b)}2&lt;p.
$$</div>
<p>With $\lambda=4b+\kappa b(1-2b)/2$, this gives</p>
<div class="math-display">$$\xi:=\lambda-2b-1=(2b-1)(1-\kappa b/2)&gt;0.$$</div>
<p>At the fine grid level $n\geq0$, split according to whether $M\leq n$. On that event the window is contained in $[-2n-8,2n+8]$. Summing <a href="/tag/EG6U/">EG6U</a> over this deterministic interval bounds the expected contribution of the $a$th powers by</p>
<div class="math-display">$$C_{h,\kappa,b}(n+1)^{2b+1}2^{-n\xi}.$$</div>
<p>On $\{M&gt;n\}$, Schwarz–Pick and the reverse-flow height bound give $A_{j,n}\leq\sqrt5$. There are at most $C(1+M)2^n$ grid points in the random window, so this contribution is at most</p>
<div class="math-display">$$C_{\kappa,b}2^n\mathbb E[(1+M)\mathbf1_{\{M&gt;n\}}]
\leq C_{\kappa,b}2^n e^{-c_\kappa n^2}.$$</div>
<p>The last bound follows from the reflection-principle Gaussian tail of $M$, after decreasing $c_\kappa&gt;0$ to absorb the polynomial factor. Both displayed bounds are summable in $n$. At heights two and four there are only $O(1+M)$ grid points, and their derivative scales are at most $\sqrt{20}$, so their expected contribution is finite. Finally, at every included height, $A_{j,n}^p\leq20^{(p-a)/2}A_{j,n}^a$. This proves the asserted moment bound.</p>

## The Whitney moment threshold {#section-whitney-threshold}

<a id="tag-J0CG" data-assertion="theorem" data-title="Expected SLE Whitney sums are finite exactly above the boundary exponent away from kappa four"></a>
<p>For each $\kappa&gt;0$, $\kappa\ne4$, there is $h_0&gt;0$ such that for every $0&lt;h\leq h_0$ and $p&gt;0$,</p>
<div class="math-display">$$\mathbb E[S_h(p)]
\begin{cases}&lt;\infty,&p&gt;\delta(\kappa),\\
=\infty,&0&lt;p\leq\delta(\kappa).
\end{cases}$$</div>
<p>The finiteness assertion in fact holds for every $h&gt;0$.</p>
<p><em>Proof.</em> The upper assertion follows immediately from IDL1 and HQI8. For divergence, take $h_0$ from the localized threshold <a href="/tag/T3F8/">T3F8</a>, and fix the horizontal window $L=1$. Then</p>
<div class="math-display">$$\mathbb E[J_{\delta(\kappa),h_0,1}(F)]=\infty.$$</div>
<p>Choose $0&lt;\varepsilon_0&lt;\min\{h_0/4,1/4\}$ and $q&gt;\delta(\kappa)$. The contribution from grid points with $A_{j,n}&gt;\varepsilon_0$ has finite expectation, because</p>
<div class="math-display">$$A_{j,n}^{\delta(\kappa)}\mathbf1_{\{A_{j,n}&gt;\varepsilon_0\}}
\leq\varepsilon_0^{\delta(\kappa)-q}A_{j,n}^q$$</div>
<p>and <a href="/tag/AVHR/">AVHR</a> bounds the expected localized $q$th-power sum. The remaining sum, restricted to $A_{j,n}\leq\varepsilon_0$, must therefore still have infinite expectation.</p>
<p>Let $z=F(z_{j,n})$ be one of these remaining image points. Its height is at least $h_0$, whereas Koebe's quarter theorem gives</p>
<div class="math-display">$$\operatorname{dist}(z,\partial D)\leq2A_{j,n}
\leq2\varepsilon_0&lt;\min\{h_0/2,1/2\}.$$</div>
<p>A nearest boundary point cannot lie on the real line, so it belongs to $K$. Hence the Whitney square $Q$ containing $z$ satisfies $\operatorname{dist}(Q,K)&lt;1$ and $\sup\operatorname{Im}Q\geq h_0$. It belongs to $\mathcal W_h$ for every $h\leq h_0$. The Whitney distance bounds and Koebe give $A_{j,n}\asymp d(Q)$.</p>
<p>Distinct dyadic grid points are separated by at least $\log2$ in the hyperbolic metric of $\mathbb H$. Their images have the same separation in $D$. Since a Whitney square has uniformly bounded hyperbolic diameter, hyperbolic packing bounds the number of these images it contains by an absolute constant. Assign points on square boundaries by a fixed ordering. Thus the remaining grid sum is at most $C_\kappa S_h(\delta(\kappa))$, proving infinite expectation at the threshold. For $0&lt;p&lt;\delta(\kappa)$, every square in $\mathcal W_h$ has $d(Q)\leq1$, so $d(Q)^p\geq d(Q)^{\delta(\kappa)}$. This proves the remaining cases.</p>
<p>This proves Rohde–Schramm Theorem 8.3. The argument transfers sums directly between Whitney squares and the full inverse-map grid; it does not require the source's comparison restricted to the boundary preimage interval.</p>

## Expected coverings of the boundary {#section-covering-lower}

<p>Let $N(\varepsilon,E)$ be the least number of open disks of radius $\varepsilon$ covering a bounded set $E$.</p>

<a id="tag-K5PX" data-assertion="corollary" data-title="Expected SLE boundary covering numbers have an unbounded critical rescaling with every summable logarithmic loss"></a>
<p>For $\kappa&gt;0$, $\kappa\ne4$, and every sufficiently small fixed $h&gt;0$, one has, for every $\eta&gt;0$,</p>
<div class="math-display">$$\limsup_{\varepsilon\downarrow0}
\bigl(\log(1/\varepsilon)\bigr)^{1+\eta}\varepsilon^{\delta(\kappa)}
\mathbb E\!\left[N\bigl(\varepsilon,\partial K\cap\{\operatorname{Im}z&gt;h\}\bigr)\right]
=\infty.$$</div>
<p>For each fixed positive $\varepsilon$ the expectation is finite, since the hull lies in $[-M,M]+i[0,2]$ and $\mathbb E[M]&lt;\infty$.</p>
<p><em>Proof.</em> Take $2h\leq h_0$, where $h_0$ is from J0CG, and let $W_{2h}(n)$ count the squares in $\mathcal W_{2h}$ of side $r=2^{-n}$. Suppose $r&lt;h/11$. The centre of each such square has height at least $2h-r/2$ and lies within $10r$ of $\partial D$. A nearest boundary point consequently has height greater than $h$ and belongs to $\partial K$.</p>
<p>In any cover of $E_h=\partial K\cap\{\operatorname{Im}z&gt;h\}$ by $r$-disks, assign each square to a disk containing its chosen boundary point. The square's centre is within $11r$ of that disk's centre. Squares of the same side length have disjoint interiors, so a planar area comparison bounds the number assigned to one disk by an absolute constant. Therefore</p>
<div class="math-display">$$W_{2h}(n)\leq C\,N(2^{-n},E_h)$$</div>
<p>at all sufficiently fine levels. The use of $\mathcal W_{2h}$ ensures that the boundary point lies above the height used in the covering number.</p>
<p>The coarse levels have finite expected contribution to $S_{2h}(\delta(\kappa))$. Indeed, all relevant squares lie in $[-M-3,M+3]+i[0,5]$, and squares with side bounded below have total number at most $C_h(1+M)$. Since the side lengths are dyadic and at most one, J0CG and Tonelli give</p>
<div class="math-display">$$\sum_{n=0}^{\infty}2^{-n\delta(\kappa)}
\mathbb E[N(2^{-n},E_h)]=\infty.$$</div>
<p>If the claimed limsup were finite for some $\eta&gt;0$, then along the dyadic scales the summands in this series would eventually be bounded by $C n^{-1-\eta}$. That series converges, a contradiction.</p>
<p>Taking $\eta=h$ gives the logarithmic statement of Rohde–Schramm Corollary 8.5; the same argument permits any positive $\eta$ independently of the fixed spatial cutoff. This is an expected-covering lower limsup, not an almost-sure dimension lower bound.</p>
