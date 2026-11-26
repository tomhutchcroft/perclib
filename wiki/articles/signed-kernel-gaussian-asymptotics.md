---
{
  "id": "signed-kernel-gaussian-asymptotics",
  "title": "Gaussian asymptotics for signed kernels",
  "subtitle": "Weighted heat estimates and the spatial Green function",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "A quadratic Fourier gap, a finite absolute second moment and a pointwise tail bound give the spatial Green asymptotic even for a signed kernel. A higher moment gives the quantitative remainder used by the lace expansion.",
  "context": [
    "Real kernels on $\\mathbb Z^d$, with $d>2$, invariant under coordinate sign changes and permutations.",
    "Write $\\langle x\\rangle=\\max\\{1,|x|\\}$; Fourier integrals use normalized Lebesgue measure on $[-\\pi,\\pi]^d$.",
    "The effective kernel may be signed. No probabilistic interpretation of its heat kernel is assumed."
  ],
  "related": [
    "spatial-convolution-asymptotics",
    "spatial-lace-coefficient-bounds",
    "correlation-length-fourier",
    "signed-kernel-moments"
  ],
  "sourceIds": [
    "hara-nearest-neighbour-2008",
    "heydenreich-hofstad"
  ],
  "aliases": [
    "Gaussian lemma",
    "signed heat kernel",
    "Hara Theorem 1.4"
  ],
  "prototypeUses": []
}
---

## A weighted heat estimate {#section-heat}

<p>Throughout, let $J:\mathbb Z^d\to\mathbb R$ have the symmetries in the context, and suppose</p>
<div class="math-display">$$\sum_xJ(x)=1,\qquad
M_2=\sum_x|x|^2|J(x)|<\infty,\qquad
|J(x)|\le K\langle x\rangle^{-d-2},\qquad
q(k):=1-\widehat J(k)\ge c_0|k|^2$$</div>
<p>for all $k\in[-\pi,\pi]^d$, where $c_0>0$. The mass and signed second-moment sums are absolutely convergent. Set</p>
<div class="math-display">$$M=\sum_x|x|^2J(x),\qquad a=\frac{M}{2d},\qquad
I_t(x)=\int_{[-\pi,\pi]^d}e^{ik\cdot x-tq(k)}\,\frac{dk}{(2\pi)^d}.$$</div>
<p>Symmetry and dominated Taylor expansion give $q(k)=a|k|^2+o(|k|^2)$, so $a\ge c_0>0$. The absolute second moment justifies two derivatives of $\widehat J$ and gives $|\partial_j\widehat J(k)|\le C M_2|k|$. These facts use absolute moments before any cancellation in the signed moment $M$.</p>
<a id="tag-YNLW" data-assertion="theorem" data-title="A signed heat kernel has a dimension-order spatial bound using only two Fourier derivatives"></a>
<p>Write $J_j(x)=x_jJ(x)$ and, for a multi-index $\mathbf n=(n_1,\ldots,n_d)$, let</p>
<div class="math-display">$$F_{\mathbf n,t}=I_t*J_1^{*n_1}*\cdots*J_d^{*n_d},\qquad n=\sum_jn_j.$$</div>
<p>An exponent zero means the convolution identity $\delta_0$. For every integer $0\le m\le d$ and every multi-index $\mathbf n$,</p>
<div class="math-display">$$|F_{\mathbf n,t}(x)|\le C_{m,\mathbf n}\,t^{-(d+n-m)/2}\langle x\rangle^{-m}\qquad(t>0).$$</div>
<p>In particular, $|I_t(x)|\le C\min\{t^{-d/2},\langle x\rangle^{-d}\}$. Constants depend on the displayed kernel bounds, the dimension and the indicated indices.</p>
<p><em>Proof.</em> Each $J_j$ is summable. Convolution against these kernels is therefore well-defined for the bounded Fourier integral $I_t$, and Fourier multiplication follows by absolute Fubini. For $m=0$, its integral representation and the derivative bound give</p>
<div class="math-display">$$|F_{\mathbf n,t}(x)|\le C_{\mathbf n}\int_{\mathbb R^d}|k|^n e^{-c_0t|k|^2}\,dk
\le C_{\mathbf n}t^{-(d+n)/2}.$$</div>
<p>At $x=0$ this already proves every $m\le d$ when $t\ge1$. When $t\le1$, the integral over the fixed torus is bounded uniformly in $t$, while $t^{-(d+n-m)/2}\ge1$.</p>
<p>Induct on $m$, simultaneously for all multi-indices. Put $J_{j\ell}(y)=y_jy_\ell J(y)$. One integration by parts on the torus gives the exact identity</p>
<div class="math-display">$$x_\ell F_{\mathbf n,t}(x)
=tF_{\mathbf n+\mathbf e_\ell,t}(x)
+\sum_{j:n_j>0}n_j\bigl(F_{\mathbf n-\mathbf e_j,t}*J_{j\ell}\bigr)(x).$$</div>
<p>The boundary terms cancel since $x$ has integer coordinates. Only first derivatives of the product and second derivatives of $\widehat J$ occur. In particular, this identity does not require $d$ moments or $d$ Fourier derivatives.</p>
<p>The induction hypothesis bounds the first term by $C t^{-(d+n-m)/2}\langle x\rangle^{-(m-1)}$. It gives the same bound for each $F_{\mathbf n-\mathbf e_j,t}$ before convolution. For $m=1$, convolution preserves this bound because $\|J_{j\ell}\|_1\le M_2$.</p>
<p>For $m>1$, use the following elementary endpoint estimate. If $0<b<d$, $|f(x)|\le A\langle x\rangle^{-b}$, $\|g\|_1<\infty$ and $|g(x)|\le B\langle x\rangle^{-d}$, then</p>
<div class="math-display">$$|(f*g)(x)|\le C_{b,d}A(\|g\|_1+B)\langle x\rangle^{-b}.$$</div>
<p>Indeed, for $R=|x|\ge2$, the part with $|x-y|\ge R/2$ is bounded by $C AR^{-b}\|g\|_1$. In its complement $|y|\ge R/2$, so the bound on $g$ and the shell sum of $f$ give $C ABR^{-d}R^{d-b}$. Boundedness and absolute summability cover smaller $x$.</p>
<p>Apply this with $b=m-1<d$, since $|J_{j\ell}(y)|\le K\langle y\rangle^{-d}$ and $\|J_{j\ell}\|_1\le M_2$. Thus the right-hand side of the integration-by-parts identity has the required bound with spatial exponent $m-1$. For $x\ne0$, choose $\ell$ with $|x_\ell|\ge|x|/\sqrt d$ and divide by $|x_\ell|$. This finishes the induction.</p>

## The Gaussian approximation at large times {#section-gaussian}

<a id="tag-KSC4" data-assertion="theorem" data-title="The signed heat kernel has a uniform Gaussian approximation and a higher-moment error bound"></a>
<p>Under the standing hypotheses, let</p>
<div class="math-display">$$G_t(x)=(4\pi at)^{-d/2}\exp\!\left(-\frac{|x|^2}{4at}\right).$$</div>
<p>Then</p>
<div class="math-display">$$\sup_x|I_t(x)-G_t(x)|=o(t^{-d/2})\qquad(t\to\infty).$$</div>
<p>If additionally $\sum_x|x|^{2+\rho}|J(x)|<\infty$ for some $\rho>0$, put $\alpha=\min\{\rho,2\}$. In that case</p>
<div class="math-display">$$\sup_x|I_t(x)-G_t(x)|\le C t^{-(d+\alpha)/2}\qquad(t\ge1).$$</div>
<p><em>Proof.</em> The Gaussian is the inverse Fourier integral of $e^{-at|k|^2}$ on $\mathbb R^d$. Rescale both integrals by $l=\sqrt t\,k$. The difference in their Fourier integrands, extended by zero outside the rescaled torus for the first one, tends to zero for each fixed $l$. Its absolute value is bounded by $e^{-c_0|l|^2}+e^{-a|l|^2}$. Dominated convergence in $L^1(\mathbb R^d)$ proves the first assertion, uniformly in $x$ since the oscillatory factor has modulus one.</p>
<p>For the quantitative assertion, the cosine remainder bound $|1-\cos u-u^2/2|\le C_\alpha|u|^{2+\alpha}$ and the absolute higher moment give</p>
<div class="math-display">$$|q(k)-a|k|^2|\le C|k|^{2+\alpha}.$$</div>
<p>Both $q(k)$ and $a|k|^2$ are at least $c_0|k|^2$. Hence the mean value theorem for the exponential gives, on the torus,</p>
<div class="math-display">$$|e^{-tq(k)}-e^{-at|k|^2}|
\le Ct|k|^{2+\alpha}e^{-c_0t|k|^2}.$$</div>
<p>Integration bounds this by $Ct^{-(d+\alpha)/2}$. The Gaussian integral outside the torus is exponentially small for $t\ge1$ and is absorbed in the same bound.</p>

## The spatial Green asymptotic {#section-green}

<a id="tag-OT9N" data-assertion="theorem" data-title="A signed effective kernel has the spatial Green asymptotic with an explicit amplitude and remainder"></a>
<p>Define</p>
<div class="math-display">$$U(x)=\int_{[-\pi,\pi]^d}\frac{e^{ik\cdot x}}{q(k)}\,\frac{dk}{(2\pi)^d},\qquad
A_d=\frac{d\,\Gamma(d/2-1)}{2\pi^{d/2}}.$$</div>
<p>The integral is absolutely convergent. There is a constant $C$ such that $|U(x)|\le C\langle x\rangle^{2-d}$, and</p>
<div class="math-display">$$U(x)=\frac{A_d}{M}|x|^{2-d}+o(|x|^{2-d})\qquad(|x|\to\infty).$$</div>
<p>Under the higher-moment assumption of KSC4, with $\alpha=\min\{\rho,2\}$,</p>
<div class="math-display">$$U(x)=\frac{A_d}{M}\langle x\rangle^{2-d}
+O\!\left(\langle x\rangle^{-(d-2+\alpha/d)}\right).$$</div>
<p><em>Proof.</em> The quadratic lower bound and $d>2$ make $q^{-1}$ integrable. Absolute Fubini gives $U(x)=\int_0^\infty I_t(x)\,dt$, as in <a href="/tag/ZPZZ/">ZPZZ</a>. Integrating the minimum in YNLW, with a split at $t=\langle x\rangle^2$, proves the spatial upper bound.</p>
<p>For $R=|x|>0$, direct substitution into the Gaussian integral yields</p>
<div class="math-display">$$\int_0^\infty G_t(x)\,dt
=\frac{\Gamma(d/2-1)}{4\pi^{d/2}a}R^{2-d}
=\frac{A_d}{M}R^{2-d}.$$</div>
<p>Also, maximizing $u^{d/2}e^{-u}$ with $u=R^2/(4at)$ gives the uniform-in-time bound</p>
<div class="math-display">$$G_t(x)\le\left(\frac{d}{2\pi e}\right)^{d/2}R^{-d}.$$</div>
<p>Fix $\varepsilon>0$ and split the integral of $I_t-G_t$ at $T=\varepsilon R^2$. The two short-time bounds give an absolute contribution at most $C\varepsilon R^{2-d}$. By KSC4, the remaining integral is $o(T^{1-d/2})$, which is $o(R^{2-d})$ for fixed $\varepsilon$. First let $R\to\infty$, then let $\varepsilon\downarrow0$. This proves the leading asymptotic.</p>
<p>For the quantitative assertion take $T=R^{2-\alpha/d}$, with $R\ge1$. The short-time contribution is $O(TR^{-d})=O(R^{-(d-2+\alpha/d)})$. The large-time error is at most</p>
<div class="math-display">$$C\int_T^\infty t^{-(d+\alpha)/2}\,dt
=C' T^{-(d+\alpha-2)/2}
=O\!\left(R^{-(d-2+\alpha/d)}\right).$$</div>
<p>The last inequality follows from $(d+\alpha-2)(1-\alpha/(2d))-(d-2+\alpha/d)=\alpha(d-\alpha)/(2d)>0$, since $d>2$ and $0<\alpha\le2$. A larger constant covers the origin.</p>
<p>The explicit Gaussian bound above also supplies the constant correction in the <a href="/errata/hara-nearest-neighbour-2008/#gaussian-truncation-prefactor">provisional entry for Hara's (2.23)–(2.26)</a>. Its dimension factor affects an intermediate bound, not this asymptotic or its exponent.</p>

## The effective kernel in the spatial lace equation {#section-lace}

<a id="tag-KB4O" data-assertion="corollary" data-title="The signed Gaussian lemma and convolution transfer give the spatial lace asymptotic under pointwise coefficient control"></a>
<p>Let $d>8$, let $D$ be the uniform nearest-neighbour step distribution, and let $j>0$. Suppose a real kernel $\Pi$ has the standing coordinate symmetries and</p>
<div class="math-display">$$|\Pi(x)|\le C\langle x\rangle^{-2(d-2)},\qquad
j[1+\widehat\Pi(0)]=1.$$</div>
<p>Set $J=jD*(\delta_0+\Pi)$ and assume $1-\widehat J(k)\ge c_0|k|^2$ on the torus. Let $V$ be the inverse Fourier integral of $(1-\widehat J)^{-1}$, and suppose $\tau=(\delta_0+\Pi)*V$. Then</p>
<div class="math-display">$$M=1+j\sum_x|x|^2\Pi(x)>0,\qquad
\tau(x)=\frac{A_d}{jM}\langle x\rangle^{2-d}
+O\!\left(\langle x\rangle^{-(d-2+2/d)}\right).$$</div>
<p><em>Proof.</em> A nearest-neighbour shift preserves the stated power bound up to a constant, so $J$ has the same decay exponent $2d-4$. Since $d>8$, this implies both the pointwise bound $|J(x)|\le K\langle x\rangle^{-d-2}$ and a finite absolute fourth moment. The mass of $J$ is one. Summing its second moment and using the zero mean and unit second moment of $D$ gives</p>
<div class="math-display">$$\sum_x|x|^2J(x)=j\sum_y(1+|y|^2)(\delta_0+\Pi)(y)
=1+j\sum_y|y|^2\Pi(y).$$</div>
<p>The Fourier gap makes this quantity positive. Apply OT9N with $\rho=2$ to obtain the Green expansion for $V$ with amplitude $A_d/M$ and remainder exponent $2/d$. Then <a href="/tag/I8BE/">I8BE</a> transfers it through $\delta_0+\Pi$, whose mass is $1/j$.</p>
<p>This completes the analytic deduction from the stated effective-kernel inputs. It leaves the all-order pointwise coefficient estimate and the improving spatial bootstrap to be proved for the percolation model; the first-two-coefficient result <a href="/tag/P8KQ/">P8KQ</a> does not by itself provide them. No numerical nearest-neighbour dimension threshold is asserted here.</p>

## Supplying the coefficient input {#section-pointwise-followup}

<p>The later theorem <a href="/tag/KF2I/">KF2I</a> supplies the needed pointwise tail in sufficiently large dimension using moment doubling and the planar two-edge deletion bound. It applies OT9N first with a coefficient exponent greater than $d+2$, obtains the spatial two-point asymptotic by MZ23, and then improves the coefficient exponent to $2(d-2)$. This closes the qualitative percolation application without using its desired spatial bound as an input. No numerical dimension threshold is obtained.</p>

## Balancing the two heat-kernel errors {#section-balanced-error}

<p>The time cutoff in OT9N was chosen for convenience. Balancing its two error bounds gives a stronger remainder under the same hypotheses.</p>

<a id="tag-7QGG" data-assertion="theorem" data-title="Balancing the short-time and Gaussian errors improves the signed Green remainder"></a>
<p>Under the standing signed-kernel hypotheses and $\sum_x|x|^{2+\rho}|J(x)|<\infty$, where $\rho>0$, put $\alpha=\min\{\rho,2\}$ and $\beta=2\alpha/(d+\alpha)$. Then</p>
<div class="math-display">$$U(x)=\frac{A_d}{M}\langle x\rangle^{2-d}
+O\!\left(\langle x\rangle^{-(d-2+\beta)}\right).$$</div>
<p>In particular, a finite absolute fourth moment gives remainder exponent $\beta=4/(d+2)$.</p>
<p><em>Proof.</em> Let $R=|x|\ge1$. The heat representation and Gaussian integral in OT9N give</p>
<div class="math-display">$$U(x)-\frac{A_d}{M}R^{2-d}
=\int_0^\infty\bigl[I_t(x)-G_t(x)\bigr]\,dt.$$</div>
<p>YNLW and the uniform spatial bound for $G_t$ bound the integral over $0<t<T$ by $CTR^{-d}$. KSC4 bounds the remaining integral, for $T\ge1$, by $CT^{-(d+\alpha-2)/2}$. Take $T=R^{2d/(d+\alpha)}$. The two powers coincide:</p>
<div class="math-display">$$TR^{-d}=T^{-(d+\alpha-2)/2}
=R^{-d(d+\alpha-2)/(d+\alpha)}
=R^{-(d-2+\beta)}.$$</div>
<p>This proves the bound away from the origin; absolute integrability of $q^{-1}$ covers the origin by increasing the constant. The proof uses exactly the two estimates already established, with no additional derivative, positivity or moment assumption. It does not assert that this remainder is optimal for the kernel.</p>
