---
{
  "id": "fourier-spatial-moment-bridge",
  "title": "From coefficient moments to spatial bounds",
  "subtitle": "Regularizing the critical Fourier quotient",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "Absolute coefficient moments control derivatives of the lace quotient. A denominator regularization justifies integration by parts at criticality, and positive Fejer approximations give weighted spatial convolutions without assuming summability of the two-point function.",
  "context": [
    "Real even kernels on $\\mathbb Z^d$, with $d>2$. Fourier integrals use normalized Haar measure on $[-\\pi,\\pi]^d$.",
    "The effective step kernel may be signed. A quadratic Fourier gap is an explicit hypothesis.",
    "The final percolation application uses the completed sufficiently-high-dimensional Fourier bootstrap, without a spatial bootstrap hypothesis."
  ],
  "related": ["completed-fourier-bootstrap", "higher-lace-moments", "signed-kernel-moments", "spatial-lace-coefficient-bounds", "signed-kernel-gaussian-asymptotics"],
  "sourceIds": ["hara-nearest-neighbour-2008"],
  "aliases": ["critical Fourier differentiation", "coefficient moment bridge", "weighted critical convolutions"],
  "prototypeUses": []
}
---

## Derivatives of the regularized quotient {#section-derivatives}

<p>Let $M\ge2$ be an integer. Suppose $b,J$ are real even kernels with</p>
<div class="math-display">$$\sum_x(1+|x|^M)(|b(x)|+|J(x)|)<\infty,\qquad
\sum_xJ(x)=1,\qquad F(k):=1-\widehat J(k)\ge c|k|^2$$</div>
<p>on the torus, for some $c>0$. Define</p>
<div class="math-display">$$R_\varepsilon(k)=\frac{\widehat b(k)}{\varepsilon+F(k)}\quad(0<\varepsilon\le1),\qquad
R(k)=\frac{\widehat b(k)}{F(k)}\quad(k\ne0).$$</div>
<p>Constants below may depend on the dimension, the moment bounds, $M$ and $c$; no uniformity in these inputs is asserted.</p>
<a id="tag-2ZOB" data-assertion="proposition" data-title="Absolute kernel moments control every mixed derivative of the regularized lace quotient"></a>
<p>For every multi-index $\nu$ with $0\le|\nu|\le M$,</p>
<div class="math-display">$$|\partial^\nu R_\varepsilon(k)|\le C_\nu(\varepsilon+|k|^2)^{-1-|\nu|/2}.$$</div>
<p>Consequently $|\partial^\nu R(k)|\le C_\nu|k|^{-2-|\nu|}$ away from zero. If $2+|\nu|<d$, then $\partial^\nu R_\varepsilon\to\partial^\nu R$ in $L^1$ as $\varepsilon\downarrow0$.</p>
<p><em>Proof.</em> The absolute moments justify all derivatives of $\widehat b$ and $\widehat J$ through order $M$. Put $\rho=(\varepsilon+|k|^2)^{1/2}$. Evenness and the absolute second moment give</p>
<div class="math-display">$$|\partial_jF(k)|
=\left|\sum_x x_jJ(x)\sin(k\cdot x)\right|
\le |k|\sum_x|x|^2|J(x)|.$$</div>
<p>Higher derivatives are bounded by their absolute moments. Since $\rho$ is bounded above on the torus for $\varepsilon\le1$, these estimates imply</p>
<div class="math-display">$$|\partial^\eta F(k)|\le C_\eta\rho^{2-|\eta|}\quad(1\le|\eta|\le M),\qquad
|\partial^\nu\widehat b(k)|\le C_\nu\rho^{-|\nu|}.$$</div>
<p>Also $\varepsilon+F\ge\min\{1,c\}\rho^2$. The assertion at order zero follows at once. Induct on $|\nu|$ in the differentiated identity $(\varepsilon+F)R_\varepsilon=\widehat b$:</p>
<div class="math-display">$$(\varepsilon+F)\partial^\nu R_\varepsilon
=\partial^\nu\widehat b
-\sum_{0<\eta\le\nu}\binom\nu\eta
(\partial^\eta F)(\partial^{\nu-\eta}R_\varepsilon).$$</div>
<p>Each term in the sum is bounded by a constant times $\rho^{2-|\eta|}\rho^{-2-|\nu|+|\eta|}=\rho^{-|\nu|}$. Division proves the desired estimate. The derivatives converge pointwise off zero as $\varepsilon\downarrow0$. Their common majorant $C_\nu|k|^{-2-|\nu|}$ is integrable precisely in the stated strict range, so dominated convergence gives the $L^1$ assertion.</p>

## Spatial decay without a critical Fourier series {#section-decay}

<p>Define $\tau(x)=\int e^{-ik\cdot x}R(k)\,dk$. This inverse integral exists because $d>2$. We do not assume that $\tau$ is summable.</p>
<a id="tag-1165" data-assertion="theorem" data-title="Integrable quotient derivatives give spatial decay from coefficient moments"></a>
<p>For every multi-index $\nu$ with $|\nu|\le M$ and $2+|\nu|<d$,</p>
<div class="math-display">$$x^\nu\tau(x)=i^{-|\nu|}\int e^{-ik\cdot x}\partial^\nu R(k)\,dk.$$</div>
<p>In particular, for every integer $0\le n\le M$ with $n<d-2$,</p>
<div class="math-display">$$|\tau(x)|\le C_n\langle x\rangle^{-n},\qquad \langle x\rangle=\max\{1,|x|\}.$$</div>
<p><em>Proof.</em> The function $R_\varepsilon$ is $C^M$ and periodic. Integration by parts on the torus has no boundary term, since $x$ is an integer vector, and gives the first identity with $R_\varepsilon$ and its inverse integral. The preceding proposition gives $L^1$ convergence both before and after differentiation. Passing to the limit proves the identity. In particular, the displayed derivative is also the weak derivative of the integrable function $R$; no contribution at the singular frequency has been discarded.</p>
<p>For $x\ne0$, choose a coordinate $j$ with $|x_j|\ge|x|/\sqrt d$ and take $\nu=n e_j$. The integral is bounded by its $L^1$ norm, uniformly in $x$. Division gives the power bound; the inverse integral itself bounds $x=0$. Odd $n$ cause no difficulty here: $x_j^n$ may be signed, and we take its absolute value only after the identity. No formula for the Fourier transform of $|x_j|^n\tau(x)$ is being asserted for odd $n$.</p>

## Weighted convolution sums {#section-convolutions}

<p>Suppose now that $\tau(x)\ge0$. For an even integer $m\in[0,M]$ and a coordinate $j$, write $g_{m,j}(x)=|x_j|^m\tau(x)$, interpreting the weight as one when $m=0$, and set $A_{m,j}=i^{-m}\partial_j^mR$.</p>
<a id="tag-BNKQ" data-assertion="theorem" data-title="Evenly weighted critical convolutions are finite under the Fourier power-counting condition"></a>
<p>Let $\ell\ge2$, let $m_1,\ldots,m_\ell$ be even integers between zero and $M$, and choose coordinates $j_1,\ldots,j_\ell$. If</p>
<div class="math-display">$$2\ell+\sum_{a=1}^\ell m_a<d,$$</div>
<p>then the nonnegative convolution sum is finite at every endpoint, uniformly in that endpoint, and</p>
<div class="math-display">$$(g_{m_1,j_1}*\cdots*g_{m_\ell,j_\ell})(y)
=\int e^{-ik\cdot y}\prod_{a=1}^\ell A_{m_a,j_a}(k)\,dk.$$</div>
<p>The same finiteness conclusion holds when each coordinate weight is replaced by the radial weight $|x|^{m_a}$.</p>
<p><em>Proof.</em> Choose $q_a>1$ such that $\sum_aq_a^{-1}=1$ and $q_a(2+m_a)<d$. Such a choice exists because the displayed strict inequality is equivalent to $\sum_a(2+m_a)/d<1$. The derivative bound puts $A_{m_a,j_a}$ in $L^{q_a}$, and Hölder makes their product integrable.</p>
<p>It remains to identify its Fourier coefficient with the spatial sum. This step cannot be justified by assuming summability of the individual $g_{m_a,j_a}$. Let $\mathcal F_N$ be the product Fejér kernel, normalized to have integral one. Its Fourier multiplier is</p>
<div class="math-display">$$\theta_N(x)=\prod_{j=1}^d\left(1-\frac{|x_j|}{N+1}\right)_+.$$</div>
<p>By 1165, the inverse coefficients of $\mathcal F_N*A_{m_a,j_a}$ are exactly $\theta_N(x)g_{m_a,j_a}(x)$. These have finite support and are nonnegative. Their convolution therefore equals the inverse integral of the product of the smoothed Fourier functions. Hölder and the $L^{q_a}$ contraction of convolution by a nonnegative probability kernel bound this integral in absolute value by $\prod_a\|A_{m_a,j_a}\|_{q_a}$, independently of $N$ and the endpoint.</p>
<p>The multipliers $\theta_N(x)$ increase to one. Monotone convergence in the nonnegative spatial convolution sum gives its finiteness and the same bound. On the Fourier side, Fejér approximation converges in each $L^{q_a}$: this follows first for trigonometric polynomials and then by density and the contraction bound. A telescoping product and Hölder give convergence of the products in $L^1$. Their inverse integrals consequently converge to the displayed formula. This proves both convergence and identification without an absolutely convergent critical Fourier series.</p>
<p>For even $m\ge2$, $|x|^m\le d^{m/2-1}\sum_j|x_j|^m$. Expand the finitely many coordinate choices in the resulting upper bound. Each convolution has just been bounded. The case $m=0$ needs no comparison.</p>

## The first unconditional spatial bounds {#section-percolation}

<a id="tag-CMEX" data-assertion="corollary" data-title="The completed critical Fourier bootstrap gives quadratic spatial decay and weighted bubble and triangle bounds"></a>
<p>For nearest-neighbour bond percolation in sufficiently large dimension,</p>
<div class="math-display">$$\tau_{p_c}(x)\le C_d\langle x\rangle^{-2}.$$</div>
<p>After requiring $d>8$, the following quantities are also finite:</p>
<div class="math-display">$$\begin{aligned}
&\sup_y\sum_x |x|^2|y-x|^2\tau_{p_c}(x)\tau_{p_c}(y-x),\\
&\sup_y\sum_{x,z}|x|^2\tau_{p_c}(x)\tau_{p_c}(z-x)\tau_{p_c}(y-z),\\
&\sup_y\tau_{p_c}^{*4}(y).
\end{aligned}$$</div>
<p>In particular $\sum_x|x|^4\tau_{p_c}(x)^2<\infty$. The same bounds hold uniformly for $0\le p\le p_c$ after replacing every two-point function by $\tau_p$.</p>
<p><em>Proof.</em> <a href="/tag/F7N7/">F7N7</a> gives the critical inverse Fourier representation with</p>
<div class="math-display">$$b=\delta_0+\Pi_{p_c},\qquad J=j_cD*b,\qquad \sum J=1,$$</div>
<p>absolute second moments for $b$, and a lower bound for $1-\widehat J$ by a positive constant times $1-\widehat D$. Since $D$ has finite support, <a href="/tag/QA8C/">QA8C</a> gives an absolute second moment for $J$. On the torus, $1-\widehat D(k)\ge2|k|^2/(\pi^2d)$. All hypotheses above therefore hold with $M=2$, without assuming a spatial decay estimate.</p>
<p>Apply 1165 with $n=2$ for the first conclusion. The three convolution bounds follow from BNKQ with the respective weights $(2,2)$, $(2,0,0)$ and $(0,0,0,0)$. In each case the sum of the Fourier singularity exponents is eight, so $d>8$ suffices once the high-dimensional bootstrap is available. At endpoint zero the first bound is the asserted fourth-weighted bubble. Finally $\tau_p\le\tau_{p_c}$ and every summand is nonnegative, which proves uniformity in $p$.</p>
<p>This starts the spatial argument from the completed Fourier theorem. The fourth-weighted bubble is not a fourth moment of the lace coefficients or of $\tau_{p_c}$ itself. Promoting the coefficient moments requires the two-mark diagram estimate; extracting the two long segments for a pointwise coefficient bound requires the separated-segment analysis. Those steps, the full $|x|^{2-d}$ spatial bound and its asymptotic remain unfinished. No numerical dimension threshold or new Lean proof is asserted.</p>

## Subsequent all-order moment estimate {#section-planar-followup}

<p>The all-order moment step described above is now supplied, in sufficiently large dimension, by <a href="/tag/KOTM/">the planar Fourier estimate</a>. It handles arbitrary positions of two marks and preserves summable decay in the lace order. <a href="/tag/GIN9/">Its application</a> gives higher moments and weighted critical continuity of the entire series without a spatial hypothesis. The sharper dimension range, the separated-long-segment estimate and the full spatial asymptotic remain separate.</p>

## Subsequent fractional-weight estimates {#section-fractional-followup}

<p>The <a href="/articles/fractional-fourier-weights/">fractional-weight article</a> extends the Fourier density and convolution arguments to real coordinate powers. It uses symmetric differences to obtain the absolute weight, gives explicit strict moment and integrability conditions, and justifies the critical convolution identity by positive Fejér approximations. The later <a href="/tag/KF2I/">spatial theorem</a> supplies the coefficient moments needed for its high-dimensional application.</p>
