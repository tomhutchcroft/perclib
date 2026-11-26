---
{
  "id": "correlation-length-fourier",
  "title": "Correlation length and the critical Fourier singularity",
  "subtitle": "Second moments, reciprocal mass and the scope of Fourier asymptotics",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "The lace equation gives an exact second-moment identity and the near-critical square-root correlation-length law. Absolute coefficient moments identify the critical Fourier amplitude. Exponential tilting and spatial asymptotics require additional estimates.",
  "context": [
    "Nearest-neighbour Bernoulli bond percolation on $\\mathbb Z^d$; $p$ is the bond probability and $j=2dp$.",
    "The second-moment length is $\\xi_2(p)^2=\\chi(p)^{-1}\\sum_x|x|^2\\tau_p(x)$, without a factor $1/(2d)$.",
    "Large-dimension conclusions use the completed classical bootstrap; no numerical dimension threshold is asserted."
  ],
  "related": [
    "completed-fourier-bootstrap",
    "signed-kernel-moments",
    "triangle-susceptibility",
    "fourier-bootstrap"
  ],
  "sourceIds": [
    "heydenreich-hofstad"
  ],
  "aliases": [
    "second-moment correlation length",
    "critical Fourier amplitude",
    "inverse susceptibility and mass"
  ],
  "prototypeUses": []
}
---

## The second-moment identity {#section-moment}

<p>Put $b_p(k)=1+\widehat\Pi_p(k)$, $b_0=b_p(0)$ and $s_p=\sum_x|x|^2\Pi_p(x)$. The last sum is signed; all differentiations below require its absolute counterpart to be finite.</p>
<a id="tag-CM3M" data-assertion="proposition" data-title="The lace quotient gives an exact identity for the squared second-moment length"></a>
<p>Suppose $p<p_c$, $\Pi_p$ is even, $\sum_x(1+|x|^2)|\Pi_p(x)|<\infty$, $b_0\ne0$, and the lace quotient holds in a neighbourhood of zero:</p>
<div class="math-display">$$\widehat\tau_p(k)=\frac{b_p(k)}{1-j\widehat D(k)b_p(k)}.$$</div>
<p>Then</p>
<div class="math-display">$$\xi_2(p)^2=j\chi(p)+\frac{1+j\chi(p)}{b_0}\,s_p.$$</div>
<p><em>Proof.</em> <a href="/tag/8LOF/">8LOF</a> gives the finite second moment of $\tau_p$. Absolute moments justify differentiating its Fourier series and that of $\Pi_p$ twice. Write $F=1-j\widehat D b_p$. Evenness makes all first derivatives at zero vanish. Since $\widehat D(0)=1$, $-\sum_i\partial_{ii}\widehat D(0)=1$, and $F(0)=b_0/\chi$, differentiation of the quotient gives</p>
<div class="math-display">$$-\sum_i\partial_{ii}\widehat\tau_p(0)
=\frac{s_p}{F(0)}+\frac{j b_0(b_0+s_p)}{F(0)^2}.$$</div>
<p>Divide by $\chi$ and substitute $F(0)=b_0/\chi$. The two terms containing $s_p$ combine to the displayed identity. The formula concerns $\xi_2^2$, as is also clear from its definition; the <a href="/errata/heydenreich-hofstad/#second-moment-square">provisional notation entry</a> records the missing square in the manuscript's intermediate formula.</p>

## The near-critical scale {#section-nearcritical}

<a id="tag-93RC" data-assertion="theorem" data-title="The second-moment correlation length has the mean-field scale near criticality"></a>
<p>There are absolute $d_0,C<\infty$ such that, for $d\ge d_0$ and $p_c/2\le p<p_c$,</p>
<div class="math-display">$$\left|\frac{\xi_2(p)^2}{2dp\,\chi(p)}-1\right|\le\frac Cd.$$</div>
<p>Consequently there are absolute constants $0<c<C'<\infty$ such that, on the same range,</p>
<div class="math-display">$$\frac{c}{d(p_c-p)}\le\xi_2(p)^2\le\frac{C'}{d(p_c-p)}.$$</div>
<p>In particular, for each sufficiently large fixed dimension, $\xi_2(p)\asymp(p_c-p)^{-1/2}$ as $p\uparrow p_c$.</p>
<p><em>Proof.</em> <a href="/tag/MYG7/">MYG7</a> supplies the lace quotient and $\|\Pi_p\|_1+\sum_x|x|^2|\Pi_p(x)|\le C_0/d$ uniformly below criticality. Thus $b_0=1+O(1/d)$ and $|s_p|=O(1/d)$. Also <a href="/tag/F7N7/">F7N7</a> gives $1\le2dp_c\le1+C_0/d$. On the stated interval, $j\ge1/2$, while $\chi\ge1$. Dividing CM3M by $j\chi$ therefore bounds its error by</p>
<div class="math-display">$$\frac{|s_p|}{|b_0|}\left(1+\frac1{j\chi}\right)=O(1/d),$$</div>
<p>with an absolute constant. Increase $d_0$ so that this error is at most $1/2$.</p>
<p>To estimate $\chi$, put $\eta_c=\sup_x[\tau_c^{*3}(x)-\mathbf1_{\{x=0\}}]$. The first-step comparison in <a href="/tag/C2V4/">C2V4</a> gives $\eta_c\le3T_c=O(1/d)$. Hence every neighbouring triangle is at most $\eta_c<1/2$ in sufficiently large dimensions. <a href="/tag/0Y4K/">0Y4K</a> now yields</p>
<div class="math-display">$$\frac1{2d(p_c-p)}\le\chi(p)\le\frac1{d(p_c-p)}.$$</div>
<p>Combine this with the first estimate and $1/2\le j\le2$. This proves the bounds with absolute constants, retaining the dimension factor. At $p=0$, on the other hand, $\tau_0=\delta_0$ and $\xi_2(0)=0$. A positive lower constant times $(p_c-p)^{-1/2}$ cannot hold throughout the entire subcritical interval. The <a href="/errata/heydenreich-hofstad/#correlation-length-nearcritical-scope">scope entry</a> restricts the comparison to a neighbourhood of $p_c$.</p>

## The critical Fourier amplitude {#section-fourier}

<a id="tag-ET10" data-assertion="theorem" data-title="Absolute lace moments determine the critical Fourier amplitude and its remainder"></a>
<p>In sufficiently large dimension let $Q_c$ be the integrable Fourier density of F7N7, and set</p>
<div class="math-display">$$a_c=1+j_c\sum_x|x|^2\Pi_c(x),\qquad j_c=2dp_c.$$</div>
<p>Then $a_c=1+O(1/d)>0$ and, as $k\to0$ through nonzero frequencies,</p>
<div class="math-display">$$Q_c(k)=\frac{2d}{j_ca_c|k|^2}[1+o(1)],\qquad
Q_c(k)[1-\widehat D(k)]\longrightarrow\frac1{j_ca_c}=1+O(1/d).$$</div>
<p>If, in addition, $\sum_x|x|^{2+\varepsilon}|\Pi_c(x)|<\infty$ for some $\varepsilon>0$, the first relative error is $O(|k|^{\min\{\varepsilon,2\}})$. The additional moment is a hypothesis of this sharper remainder, not a consequence of the second-moment bound alone.</p>
<p><em>Proof.</em> The coefficient construction preserves coordinate reflections and permutations. F7N7 gives $j_c(1+\widehat\Pi_c(0))=1$ and the absolute second moment $O(1/d)$. Thus <a href="/tag/22TW/">22TW</a> applies, and its sufficient positivity condition holds for large $d$. Its quadratic expansion and the already justified density formula give the first equivalent. Since $1-\widehat D(k)=|k|^2/(2d)+O(|k|^4)$, the second limit follows.</p>
<p>For the remainder, put $\rho=\min\{\varepsilon,2\}$. The elementary bound</p>
<div class="math-display">$$|1-\cos u-u^2/2|\le C_\rho|u|^{2+\rho}$$</div>
<p>holds for all real $u$: use Taylor's formula when $|u|\le1$ and a quadratic bound otherwise. The kernel $j_cD*(\delta_0+\Pi_c)$ has a finite absolute $(2+\rho)$-moment, since $D$ is supported on unit steps. Summing the bound and using the coordinate symmetries gives</p>
<div class="math-display">$$1-j_c\widehat D(k)[1+\widehat\Pi_c(k)]
=\frac{a_c}{2d}|k|^2+O(|k|^{2+\rho}).$$</div>
<p>The numerator is $j_c^{-1}+O(|k|^2)$. Divide by the positive leading quadratic term; for sufficiently small $k$ the relative denominator error is at most $1/2$. Inverting $1+O(|k|^\rho)$ proves the claimed remainder. Constants in this local remainder may depend on the dimension and the higher moment.</p>
<p>This is a statement about a critical Fourier density, not an absolutely convergent critical Fourier series. Nor does a singularity at zero alone justify pointwise asymptotics of $\tau_c(x)$: Fourier inversion involves all frequencies and requires further error estimates for that purpose.</p>

## Exponential tilting and reciprocal susceptibility {#section-tilted}

<p>The exponential correlation length involves a different argument. The following conditional calculation isolates the normalization without assuming that its tilted coefficient bounds have already been proved.</p>
<a id="tag-1BG0" data-assertion="proposition" data-title="A tilted lace pole compares inverse susceptibility with the squared mass"></a>
<p>Fix $p<p_c$. Suppose the even kernels satisfy $\tau=\delta_0+\Pi+jD*(\delta_0+\Pi)*\tau$. Let $0<m\le1$ and assume</p>
<div class="math-display">$$\sum_x e^{m|x_1|}|\Pi(x)|<\infty,\qquad
\chi_t=\sum_xe^{tx_1}\tau(x)<\infty\ (0\le t<m),\qquad
\chi_t\longrightarrow\infty\quad(t\uparrow m).$$</div>
<p>Write $b_t=1+\sum_xe^{tx_1}\Pi(x)$ and $D_t=1+(\cosh t-1)/d$. If $b_0\ne0$, then</p>
<div class="math-display">$$jD_mb_m=1,\qquad
\frac1\chi=j\left[D_m-1+D_m\frac{b_m-b_0}{b_0}\right].$$</div>
<p>If also $1/2\le j\le2$, $1/2\le b_0\le3/2$ and $|b_m-b_0|\le m^2/(16d)$, then</p>
<div class="math-display">$$\frac{m^2}{8d}\le\frac1\chi\le\frac{2m^2}{d},\qquad
\frac{d}{2m^2}\le\chi\le\frac{8d}{m^2}.$$</div>
<p><em>Proof.</em> For $t<m$, absolute weighted summability permits Fubini in the convolution identity. It gives $\chi_t=b_t+jD_tb_t\chi_t$, and hence $1-jD_tb_t=b_t/\chi_t$. The endpoint weighted bound makes $b_t\to b_m$ by dominated convergence. Letting $t\uparrow m$ proves $jD_mb_m=1$. At $t=0$, the same identity gives $1/\chi=1/b_0-j$. Substitute the endpoint relation to obtain the second formula.</p>
<p>For $0<m\le1$,</p>
<div class="math-display">$$\tfrac12m^2\le\cosh m-1\le\tfrac{11}{20}m^2,\qquad D_m<2.$$</div>
<p>The upper estimate follows by bounding each term in the power series by its value at $m=1$ after factoring $m^2$, and using $\cosh1-1<11/20$. The correction term in brackets has absolute value at most $m^2/(4d)$. Thus the bracket lies between $m^2/(4d)$ and $4m^2/(5d)$. Multiplication by $j\in[1/2,2]$ gives the stated, slightly weaker bounds; inversion is legitimate because all quantities are positive.</p>
<p>The small quantity is $\chi^{-1}$, of order $m^2/d$. The <a href="/articles/tilted-susceptibility/#section-mass">mass identification and boundary-divergence proof</a> supplies the assumptions on $\chi_t$ at the true inverse exponential correlation length. The <a href="/articles/tilted-fourier-bootstrap/#section-length">completed tilted bootstrap</a> now supplies the coefficient inputs too, and proves the exponential correlation-length law in a stated near-critical interval for sufficiently large dimension. The <a href="/errata/heydenreich-hofstad/#mass-susceptibility-reciprocal">provisional reciprocal entry</a> records the full written correction in that regime; the numerical dimension threshold remains separate.</p>

## Continuity of the spatial bootstrap {#section-continuity}

<a id="tag-BT9V" data-assertion="proposition" data-title="Subcritical exponential moments give continuity of polynomially weighted spatial suprema"></a>
<p>For nearest-neighbour percolation, every compact parameter interval $[0,b]\subset[0,p_c)$ admits $\alpha>0$ such that $\sum_xe^{\alpha|x|}\tau_b(x)<\infty$. For every fixed $s\ge0$,</p>
<div class="math-display">$$p\longmapsto\sup_x(1+|x|)^s\tau_p(x)$$</div>
<p>is finite and continuous on $[0,p_c)$. The same conclusion holds with weight $(|x|\vee1)^s$.</p>
<p><em>Proof.</em> Apply the finite-box first-exit construction of 8LOF at $b$. It produces finite-support nonnegative kernels $K,v$ with $q=\|K\|_1<1$ and $\tau_b\le\sum_{n\ge0}K^{*n}*v$. If the supports of $K$ and $v$ lie in Euclidean balls of radii $L$ and $R$, then</p>
<div class="math-display">$$\sum_xe^{\alpha|x|}(K^{*n}*v)(x)
\le e^{\alpha R}\|v\|_1(qe^{\alpha L})^n.$$</div>
<p>Choose $\alpha>0$ so that $qe^{\alpha L}<1$. When $q=0$ the bound has only its zeroth term. Summing proves the exponential moment, and monotonicity gives the same domination for every $p\le b$.</p>
<p>Fix $p<p_c$ and choose $b\in(p,p_c)$. Pointwise continuity of $\tau_p(x)$ under the uniform-edge coupling is proved in 8LOF. The differences for parameters near $p$ are dominated by $2\tau_b$, whose every polynomial moment is finite. Dominated convergence therefore gives</p>
<div class="math-display">$$\sum_x(1+|x|)^s|\tau_{p'}(x)-\tau_p(x)|\longrightarrow0.$$</div>
<p>This sum bounds the difference of the two weighted suprema, proving continuity without assuming a maximizing vertex exists. The proof is one-sided at zero. Taking $s=d-2$ for $d\ge2$ supplies the continuity input in the manuscript's spatial bootstrap; the improving implication remains a separate estimate.</p>

## The heat integral for a signed kernel {#section-heat}

<a id="tag-ZPZZ" data-assertion="proposition" data-title="A quadratic Fourier lower bound justifies the heat-integral representation without positivity of the kernel"></a>
<p>Let $d>2$ and let $J\in\ell^1(\mathbb Z^d)$ be real and even, with $\sum_xJ(x)=1$. Suppose that for representatives $k\in[-\pi,\pi]^d$,</p>
<div class="math-display">$$1-\widehat J(k)\ge c|k|^2\qquad(c>0).$$</div>
<p>Using normalized torus measure, define</p>
<div class="math-display">$$U(x)=\int\frac{e^{-ik\cdot x}}{1-\widehat J(k)}\,dk,\qquad
I_t(x)=\int e^{-ik\cdot x}e^{-t[1-\widehat J(k)]}\,dk.$$</div>
<p>The first integral is absolutely convergent, and $U(x)=\int_0^\infty I_t(x)\,dt$ with an absolutely convergent time integral. No assumption $J(x)\ge0$ is needed.</p>
<p><em>Proof.</em> Evenness makes the Fourier transform real. Except at zero its gap is positive. Tonelli applied to the absolute value of the integrand gives</p>
<div class="math-display">$$\int\!\int_0^\infty e^{-t[1-\widehat J(k)]}\,dt\,dk
=\int\frac{dk}{1-\widehat J(k)}\le c^{-1}\int|k|^{-2}\,dk<\infty.$$</div>
<p>The single frequency zero has measure zero. Fubini now interchanges the integrals with the Fourier phase included, and the elementary Laplace integral proves the identity. In particular $\int_0^\infty|I_t(x)|\,dt$ is bounded by the same finite double integral. This argument justifies the representation, but supplies neither a spatial Gaussian approximation to $I_t$ nor its error estimates.</p>
<p>The <a href="/coverage/sources/heydenreich-hofstad-2017-correlation-fourier/">Chapter 11 reading map</a> separates these completed deductions from the higher-moment, tilted-bootstrap and spatial-asymptotic inputs.</p>
