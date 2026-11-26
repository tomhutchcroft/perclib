---
{
  "id": "spatial-convolution-asymptotics",
  "title": "Spatial convolution asymptotics",
  "subtitle": "Preserving the leading term and controlling its remainder",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "A summable kernel preserves a power-law leading term under a mild pointwise bound. Quantitative remainders depend on cancellation: an arbitrary shift produces a first-order error, while an even kernel cancels that term.",
  "context": [
    "Real kernels on $\\mathbb Z^d$ and absolutely convergent convolution sums.",
    "Write $\\langle x\\rangle=\\max\\{1,|x|\\}$ with Euclidean norm.",
    "The percolation application is conditional on the stated spatial Green-function and lace-coefficient estimates."
  ],
  "related": [
    "correlation-length-fourier",
    "signed-kernel-moments",
    "critical-arm-bounds",
    "lace-coefficient-diagrams"
  ],
  "sourceIds": [
    "hara-nearest-neighbour-2008",
    "heydenreich-hofstad"
  ],
  "aliases": [
    "convolution remainder",
    "spatial Green asymptotics",
    "cancellation in convolution"
  ],
  "prototypeUses": []
}
---

## Power-law convolution bounds {#section-bounds}

<a id="tag-IDIL" data-assertion="proposition" data-title="Power-law convolution bounds away from logarithmic endpoints"></a>
<p>Suppose $|f(x)|\le A\langle x\rangle^{-a}$ and $|g(x)|\le B\langle x\rangle^{-b}$, where $a,b>0$ and $A,B\ge0$. There is a constant depending only on $a,b,d$ such that</p>
<div class="math-display">$$|(f*g)(x)|\le C AB\begin{cases}
\langle x\rangle^{-\min\{a,b\}},&\max\{a,b\}>d,\\
\langle x\rangle^{-(a+b-d)},&a,b<d<a+b.
\end{cases}$$</div>
<p>Both assertions include absolute convergence. No claim is made here at the remaining logarithmic endpoints.</p>
<p><em>Proof.</em> For $R=|x|\ge2$, split the sum into $|y|\le R/2$, $|x-y|\le R/2$, and the region where both distances exceed $R/2$, assigning any overlap to one region. The first two contributions are bounded by</p>
<div class="math-display">$$C AB R^{-a}\sum_{|y|\le R/2}\langle y\rangle^{-b},\qquad
C AB R^{-b}\sum_{|z|\le R/2}\langle z\rangle^{-a}.$$</div>
<p>A lattice shell count bounds the partial sum with exponent $u$ by $C_uR^{d-u}$ if $u<d$, by $C\log R$ if $u=d$, and by a constant if $u>d$. In the third region, its part with $|y|\le2R$ is at most $C AB R^{d-a-b}$. For $|y|>2R$, one has $|x-y|>|y|/2$, so the same bound follows by summing dyadic shells, since $a+b>d$ in both cases under consideration.</p>
<p>If $a,b<d$, all terms have the second stated power. Otherwise suppose, by symmetry, that $a\le b$ and $b>d$. The first contribution is $O(R^{-a})$. In the second, the partial sum gives either $O(R^{d-a-b})$, $O(R^{-b}\log R)$ when $a=d$, or $O(R^{-b})$ when $a>d$; each is $O(R^{-a})$. The third contribution is no larger. The finitely many $x$ with $|x|<2$ are covered by the same summable tail and a larger constant.</p>

## A summable kernel preserves the leading coefficient {#section-leading}

<a id="tag-NIAD" data-assertion="theorem" data-title="A signed summable kernel transfers a spatial power-law leading term"></a>
<p>Let $0<a<d$ and suppose</p>
<div class="math-display">$$f(x)=A|x|^{-a}+o(|x|^{-a}),\qquad
\sum_y|g(y)|<\infty,\qquad |g(y)|\le K\langle y\rangle^{-d}.$$</div>
<p>Then the convolution is absolutely convergent and</p>
<div class="math-display">$$(f*g)(x)=A\left(\sum_yg(y)\right)|x|^{-a}+o(|x|^{-a}).$$</div>
<p>The formula remains meaningful when the signed sum of $g$ is zero.</p>
<p><em>Proof.</em> The assumed asymptotic and the finitely many remaining values give $|f(x)|\le M\langle x\rangle^{-a}$. Absolute convergence follows from boundedness of $f$ and summability of $g$. Fix $0<\varepsilon<1/3$, put $R=|x|$, and split into $|y|<\varepsilon R$, $|x-y|<\varepsilon R$, and their complement. The first two regions are disjoint.</p>
<p>In the first region the exact decomposition is</p>
<div class="math-display">$$f(x-y)=A R^{-a}
+A\bigl(|x-y|^{-a}-R^{-a}\bigr)
+\bigl(f(x-y)-A|x-y|^{-a}\bigr).$$</div>
<p>The first term, summed against $g$, equals $A R^{-a}\sum_yg(y)+o(R^{-a})$ because the omitted absolute tail tends to zero. The second is bounded in absolute value by $C\varepsilon R^{-a}\|g\|_1$. The third is $o(R^{-a})$, uniformly over this region for fixed $\varepsilon$, by the definition of the full spatial asymptotic.</p>
<p>In the second region, $|y|\ge(1-\varepsilon)R$. The pointwise bound on $g$ and the lattice shell sum give</p>
<div class="math-display">$$\sum_{|x-y|<\varepsilon R}|f(x-y)g(y)|
\le C K M R^{-d}(\varepsilon R)^{d-a}
=C K M\varepsilon^{d-a}R^{-a}$$</div>
<p>for sufficiently large $R$. In the complement, $|f(x-y)|\le M(\varepsilon R)^{-a}$, while $\sum_{|y|\ge\varepsilon R}|g(y)|\to0$. Its contribution is therefore $o(R^{-a})$ for each fixed $\varepsilon$. After multiplying the total error by $R^a$, its limit superior is at most a constant times $\varepsilon+\varepsilon^{d-a}$. Let $\varepsilon\downarrow0$.</p>
<p>The signs in the displayed decomposition matter for its exact equality, although the subsequent absolute estimates ignore them. The <a href="/errata/hara-nearest-neighbour-2008/#convolution-decomposition-sign">provisional entry for Hara's (B.18)</a> corrects the middle difference without changing any estimate or conclusion.</p>

## Quantitative remainder and cancellation {#section-remainder}

<a id="tag-MZ23" data-assertion="theorem" data-title="Evenness extends the convolution remainder from exponents below one to exponents below two"></a>
<p>Let $d>2$, put $s=d-2$, and suppose</p>
<div class="math-display">$$f(x)=A\langle x\rangle^{-s}+h(x),\qquad
|h(x)|\le B\langle x\rangle^{-(s+\rho)},\qquad
|g(x)|\le K\langle x\rangle^{-(d+\rho)}.$$</div>
<p>If $0<\rho<1$, then</p>
<div class="math-display">$$(f*g)(x)=A\left(\sum_yg(y)\right)\langle x\rangle^{-s}
+O\!\left(K(|A|+B)\langle x\rangle^{-(s+\rho)}\right).$$</div>
<p>If $g$ is even, the same conclusion holds for every $0<\rho<2$. The constants depend only on $d,\rho$. Evenness of $f$ is unnecessary.</p>
<p><em>Proof.</em> Since $s+\rho<d$ and $d+\rho>d$ in the stated ranges, IDIL gives $|h*g(x)|\le C BK\langle x\rangle^{-(s+\rho)}$. It remains to estimate</p>
<div class="math-display">$$\sum_yg(y)\bigl[F(x-y)-F(x)\bigr],\qquad F(x)=\langle x\rangle^{-s}.$$</div>
<p>Take $R=|x|\ge4$. For $|y|\le R/2$, the gradient of $|z|^{-s}$ along the segment from $x$ to $x-y$ is bounded by $C R^{-s-1}$. The near contribution is therefore bounded by</p>
<div class="math-display">$$C R^{-s-1}\sum_{|y|\le R/2}|y|\,|g(y)|
\le C K R^{-s-1}R^{1-\rho}=C K R^{-s-\rho}\qquad(0<\rho<1).$$</div>
<p>If $g$ is even, pair $y$ and $-y$ in the symmetric near region. The bracket becomes $[F(x-y)+F(x+y)-2F(x)]/2$. Its linear terms cancel, and the Hessian bound gives $C R^{-s-2}|y|^2$ instead. Since</p>
<div class="math-display">$$\sum_{|y|\le R/2}|y|^2|g(y)|\le C K R^{2-\rho}\qquad(0<\rho<2),$$</div>
<p>the same near-region estimate follows throughout that larger range.</p>
<p>On $|y|>R/2$, the term containing $F(x)$ is at most $C K R^{-s-\rho}$ by the tail sum of $g$. For the other term, first restrict to $|x-y|\le2R$. There $|g(y)|\le C K R^{-d-\rho}$ and $\sum_{|z|\le2R}F(z)\le C R^2$, again giving $C K R^{-s-\rho}$. On the remaining region $|x-y|>2R$, one has $|y|>|x-y|/2$, and a dyadic shell sum gives the same bound. These estimates work in either symmetry case. A larger constant covers the finitely many $x$ with $|x|<4$.</p>
<p>The strict endpoint restrictions arise from the truncated moment sums. At the corresponding endpoints those sums may grow logarithmically. The theorem does not silently discard that growth.</p>

## Why unrestricted remainders fail {#section-obstructions}

<a id="tag-UDUU" data-assertion="proposition" data-title="Translations obstruct a convolution remainder beyond its cancellation order"></a>
<p>Let $d>2$, $s=d-2$, $F(x)=\langle x\rangle^{-s}$ and $e=e_1$. Although a finitely supported kernel satisfies every polynomial decay bound,</p>
<div class="math-display">$$(F*\delta_e)(Re)-F(Re)
=sR^{-s-1}+O(R^{-s-2})$$</div>
<p>as integers $R\to\infty$. For the even kernel $g=(\delta_e+\delta_{-e})/2$,</p>
<div class="math-display">$$(F*g)(Re)-F(Re)
=\frac{s(s+1)}2R^{-s-2}+O(R^{-s-4}).$$</div>
<p>Thus an arbitrary kernel cannot preserve an error $O(R^{-s-\rho})$ for every $\rho>1$, and evenness alone does not do so for every $\rho>2$.</p>
<p><em>Proof.</em> For $R\ge2$, the first difference is $(R-1)^{-s}-R^{-s}$. Expand $(1-1/R)^{-s}$ to first order. For the second, average $(R-1)^{-s}$ and $(R+1)^{-s}$ and subtract $R^{-s}$; the odd Taylor terms cancel and the displayed quadratic coefficient remains positive. Division by $R^{-s-\rho}$ diverges in the respective ranges, proving both obstructions. These examples concern the convolution lemma itself, not a failure of the percolation spatial theorem.</p>
<p>The <a href="/errata/heydenreich-hofstad/#convolution-remainder-scope">provisional exercise entry</a> records the missing symmetry and exponent restrictions. MZ23 supplies a corrected statement sufficient for the book's application.</p>

## Transferring a spatial Green asymptotic {#section-transfer}

<a id="tag-I8BE" data-assertion="corollary" data-title="The spatial lace convolution preserves the Green remainder used in the high-dimensional theorem"></a>
<p>Let $d>6$. Suppose</p>
<div class="math-display">$$V(x)=A\langle x\rangle^{2-d}
+O\!\left(\langle x\rangle^{-(d-2+2/d)}\right),\qquad
|\Pi(x)|\le C\langle x\rangle^{-2(d-2)},$$</div>
<p>and $\tau=(\delta_0+\Pi)*V$. Then</p>
<div class="math-display">$$\tau(x)=A[1+\widehat\Pi(0)]\langle x\rangle^{2-d}
+O\!\left(\langle x\rangle^{-(d-2+2/d)}\right).$$</div>
<p><em>Proof.</em> Set $\rho=2/d$. Then $0<\rho<1$ and $2(d-2)>d+\rho$ for $d>6$. The kernel $g=\delta_0+\Pi$ therefore satisfies the decay hypothesis of MZ23 with this $\rho$, including at the origin after increasing its constant. Its mass is $1+\widehat\Pi(0)$, and the asserted formula follows. Absolute convergence is part of that theorem.</p>
<p>This proves the last convolution step with the same remainder as the assumed Green estimate. It does not supply the pointwise coefficient bound or the spatial Gaussian estimate for $V$. The <a href="/coverage/sources/hara-2008-convolution/">primary-source reading map</a> identifies those separate inputs.</p>


## The second-order boundary {#section-even-endpoint}

<a id="tag-7PTP" data-assertion="theorem" data-title="An even kernel gives a logarithmic remainder at the second-order boundary"></a>
<p>Let $d&gt;2$, $s=d-2$, and $F(x)=\langle x\rangle^{-s}$, with the Euclidean norm as above. Suppose $f=AF+h$ and</p>
<div class="math-display">$$
|h(x)|\le B\langle x\rangle^{-d},\qquad
|g(x)|\le K\langle x\rangle^{-d-2},\qquad g(-x)=g(x),
$$</div>
<p>where $A\in\mathbb R$ and $B,K\ge0$. Then all convolution sums below are absolutely convergent and</p>
<div class="math-display">$$
(f*g)(x)=A\left(\sum_y g(y)\right)F(x)
+O\!\left(K(|A|+B)\langle x\rangle^{-d}
             (1+\log\langle x\rangle)\right).
$$</div>
<p>The constant depends only on $d$. If $M_2=\sum_y |y|^2|g(y)|&lt;\infty$, the error is instead bounded by $C_d[|A|(K+M_2)+BK]\langle x\rangle^{-d}$.</p>
<p><em>Proof.</em> IDIL bounds $h*g$ by $C_dBK\langle x\rangle^{-d}$: one exponent equals $d$, but the other is strictly larger. For $R=|x|\ge4$, write</p>
<div class="math-display">$$
(F*g)(x)-F(x)\sum_y g(y)
=\sum_y g(y)[F(x-y)-F(x)].
$$</div>
<p>In the ball $|y|\le R/2$, evenness replaces the bracket by $[F(x-y)+F(x+y)-2F(x)]/2$. Its absolute value is at most $C_dR^{-d}|y|^2$. The truncated second absolute moment is at most $C_dK(1+\log R)$, or at most $M_2$ when that is finite.</p>
<p>Outside the ball, the term containing $F(x)$ is bounded by $C_dKR^{-d}$. For the other term, the part with $|x-y|\le2R$ is bounded by $C_dKR^{-d-2}\sum_{|z|\le2R}F(z)\le C_dKR^{-d}$; on $|x-y|&gt;2R$, both distances are comparable to $|x-y|$, and summing shells gives the same bound. Increasing the constant covers $|x|&lt;4$. $\square$</p>

## Coordinate symmetry cancels the quadratic term {#section-cubic-cancellation}

<p>The logarithm above need not occur for a lattice-symmetric kernel. The second-order Taylor term is a multiple of the Laplacian, and $|x|^{2-d}$ is harmonic away from the origin.</p>

<a id="tag-SNY9" data-assertion="theorem" data-title="Coordinate reflections and permutations extend the Green convolution remainder to fourth order"></a>
<p>Let $d&gt;2$, $s=d-2$, $2\le\rho\le4$, and suppose</p>
<div class="math-display">$$
f(x)=AF(x)+h(x),\qquad F(x)=\langle x\rangle^{-s},\qquad
|h(x)|\le B\langle x\rangle^{-s-\rho},\qquad
|g(x)|\le K\langle x\rangle^{-d-\rho}.
$$</div>
<p>Assume $g(Ux)=g(x)$ for every signed coordinate permutation $U$. The kernels may be signed; no symmetry of $h$ is required. Then</p>
<div class="math-display">$$
(f*g)(x)=A\left(\sum_y g(y)\right)F(x)
+O_{d,\rho}\!\left(K(|A|+B)\langle x\rangle^{-s-\rho}
\begin{cases}
1,&2\le\rho&lt;4,\\
1+\log\langle x\rangle,&\rho=4.
\end{cases}\right).
$$</div>
<p>In particular, no logarithm is lost at $\rho=2$. At $\rho=4$, the additional assumption $M_4=\sum_y|y|^4|g(y)|&lt;\infty$ improves the error to $O_d([|A|(K+M_4)+BK]\langle x\rangle^{-s-4})$.</p>
<p><em>Proof.</em> IDIL bounds $h*g$ by $C_{d,\rho}BK\langle x\rangle^{-s-\rho}$, including when $s+\rho\ge d$. It remains to estimate $F*g-F\sum g$. Take $R=|x|\ge4$ and expand $F(x-y)$ through degree three on the ball $|y|\le R/2$. The first- and third-degree terms sum to zero by evenness. Reflections cancel the off-diagonal second moments, and coordinate permutations make the diagonal moments equal, so for some real $m_R$,</p>
<div class="math-display">$$
\sum_{|y|\le R/2}y_i y_jg(y)=m_R\delta_{ij}.
$$</div>
<p>This is an identity of finite sums; a finite full second moment is not needed. The quadratic contribution is therefore $m_R\Delta F(x)/2=0$. Along every Taylor segment the distance from the origin is at least $R/2$, so the fourth-order remainder is bounded by $C_dR^{-s-4}|y|^4$. Thus the entire near contribution is at most</p>
<div class="math-display">$$
C_dR^{-s-4}\sum_{|y|\le R/2}|y|^4|g(y)|
\le C_{d,\rho}K R^{-s-4}
\begin{cases}
R^{4-\rho},&\rho&lt;4,\\
1+\log R,&\rho=4.
\end{cases}
$$</div>
<p>If $M_4$ is finite, use it directly instead of the last bound. On $|y|&gt;R/2$, the part containing $F(x)$ is at most $C_{d,\rho}KR^{-s-\rho}$. Where also $|x-y|\le2R$, use $|g(y)|\le C_{d,\rho}KR^{-d-\rho}$ and $\sum_{|z|\le2R}F(z)\le C_dR^2$. The remaining tail is bounded by summing $|x-y|^{-s-d-\rho}$. Both give $C_{d,\rho}KR^{-s-\rho}$. The small values of $|x|$ are absorbed in the constant. $\square$</p>
<p>For example, in dimension six, a coordinate-symmetric kernel $g=\delta_0+\Pi$ with $|\Pi(x)|\le C\langle x\rangle^{-8}$ transfers an assumed expansion $V(x)=A\langle x\rangle^{-4}+O(\langle x\rangle^{-6})$ to</p>
<div class="math-display">$$
(g*V)(x)=A[1+\widehat\Pi(0)]\langle x\rangle^{-4}
+O(\langle x\rangle^{-6}).
$$</div>
<p>This is a conditional convolution implication. It supplies neither the coefficient decay nor the assumed Green remainder at the critical dimension.</p>

## Two limits of cancellation {#section-endpoint-obstructions}

<a id="tag-1ADM" data-assertion="proposition" data-title="Even kernels can have a logarithmic second-order error and coordinate-symmetric kernels a nonzero fourth-order error"></a>
<p>Let $d&gt;2$, $s=d-2$, $F(x)=\langle x\rangle^{-s}$ and $e=e_1$. The even, nonnegative kernel</p>
<div class="math-display">$$
g(0)=0,\qquad g(y)=y_1^2|y|^{-d-4}\quad(y\ne0)
$$</div>
<p>satisfies $g(y)\le\langle y\rangle^{-d-2}$ and has, along integer $R\to\infty$,</p>
<div class="math-display">$$
(F*g)(Re)-F(Re)\sum_y g(y)\asymp R^{-d}\log R,
$$</div>
<p>with a positive difference for all sufficiently large $R$. Thus evenness alone does not remove the logarithm in 7PTP. In contrast, for the coordinate-symmetric probability kernel $D=(2d)^{-1}\sum_{i=1}^d(\delta_{e_i}+\delta_{-e_i})$,</p>
<div class="math-display">$$
(F*D)(Re)-F(Re)
=\frac{(d-2)(d-1)(d+4)}{24}R^{-d-2}
+O_d(R^{-d-4}).
$$</div>
<p>Consequently coordinate symmetry, even with finite support, does not in general give a remainder $O(R^{-s-\rho})$ for $\rho&gt;4$.</p>
<p><em>Proof.</em> For the first kernel, expand to degree three on $|y|\le R/2$. Odd terms cancel. Since $\sum_{|y|\le R/2}|y|^4g(y)\le C_dR^2$, the fourth-order remainder is $O_d(R^{-d})$. The outer region contributes $O_d(R^{-d})$ by the estimates in 7PTP.</p>
<p>Write $M_i=\sum_{0&lt;|y|\le R/2}y_i^2g(y)$. Reflections cancel the mixed moments, and permutations of coordinates $2,\ldots,d$ give $M_2=\cdots=M_d$. At $Re$, the diagonal Hessian of $F$ is $sR^{-d}\operatorname{diag}(d-1,-1,\ldots,-1)$. The quadratic contribution is therefore</p>
<div class="math-display">$$
\frac{s(d-1)}2 R^{-d}(M_1-M_2),\qquad
M_1-M_2=\frac12\sum_{0&lt;|y|\le R/2}
\frac{(y_1^2-y_2^2)^2}{|y|^{d+4}}.
$$</div>
<p>The last identity follows by exchanging the first two coordinates in half of the sum. Each dyadic annulus contributes at most a constant. For a matching lower bound, restrict to lattice points in a fixed cone around $e_1$ where $|y_1|\ge2|y_2|$ and $|y_1|\ge |y|/2$. An annulus of sufficiently large radius $r$ contains at least $c_dr^d$ such points, each contributing at least $c_dr^{-d}$. Hence $M_1-M_2\asymp\log R$. Its positive contribution dominates the $O(R^{-d})$ errors.</p>
<p>For the nearest-neighbour kernel, there is an exact expression</p>
<div class="math-display">$$
(F*D)(Re)=\frac{(R-1)^{-s}+(R+1)^{-s}
                   +2(d-1)(R^2+1)^{-s/2}}{2d}.
$$</div>
<p>Expand in $R^{-1}$. The coefficient of $R^{-s-2}$ is $s(s+2-d)/(2d)=0$, while that of $R^{-s-4}$ is</p>
<div class="math-display">$$
\frac1d\left[\frac{s(s+1)(s+2)(s+3)}{24}
                  +\frac{(d-1)s(s+2)}8\right]
=\frac{(d-2)(d-1)(d+4)}{24}&gt;0.
$$</div>
<p>The next possible order is $R^{-s-6}$, giving the stated remainder. $\square$</p>
<p>These deductions extend the earlier strict-exponent estimates. They do not alter the tagged statements of MZ23 or UDUU, establish a logarithmic loss for a coordinate-symmetric kernel, or add a new diagnosis of a published source. The source corrections and their confirmation status remain as recorded in the errata.</p>


## The corresponding walk correction {#section-walk-correction-link}

<p>The <a href="/articles/infrared-diagrams/#section-walk-green-correction">two-term nearest-neighbour Green expansion</a> identifies the directional term behind the fourth-order obstruction. Its correction to the leading Green power is proportional to $|x|^{-d}[\sum_i(x_i/|x|)^4-3/(d+2)]$, with a uniform $O(|x|^{-d-2})$ remainder. It is invariant under coordinate reflections and permutations but is not radial. This is an explicit walk calculation, separate from the model-specific spatial hypotheses in the convolution applications above.</p>



## Perturbing all factors of a marginal potential {#section-marginal-amplitude-link}

<p>The <a href="/articles/branching-random-walk/#section-convolution-amplitude-transfer">convolution amplitude transfer theorem</a> applies when a fixed bounded displacement contributes negligibly relative to the full convolution. It allows signed factors and zero limiting coefficients. For the clipped marginal walk, the known potential equivalents verify this condition even at the logarithmic boundary. Applying it to the critical percolation two-point equivalent gives <a href="/articles/branching-random-walk/#section-marginal-percolation-amplitudes">exact bubble and triangle potential amplitudes in dimension six</a>.</p>
