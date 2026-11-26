---
{
  "id": "signed-kernel-moments",
  "title": "Moments of signed convolution kernels",
  "subtitle": "Absolute summability and the quadratic Fourier term",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "Absolute second moments justify convolution and Fourier expansions for signed kernels. Nonnegative coefficient bounds supply this control for a lace sum; a bound on the signed Fourier transform alone does not.",
  "context": [
    "Real kernels on $\\mathbb Z^d$ with $d\\ge1$, counting measure and Euclidean norm.",
    "Evenness means f(x)=f(-x); coordinate reflections and permutations are stronger symmetries used only for isotropy.",
    "The critical lace application retains its weighted coefficient estimates as hypotheses."
  ],
  "related": [
    "lace-coefficient-diagrams",
    "lace-expansion",
    "infrared-diagrams"
  ],
  "sourceIds": [
    "heydenreich-hofstad"
  ],
  "aliases": [
    "signed second moments",
    "Fourier moment criterion",
    "lace dispersion"
  ],
  "prototypeUses": []
}
---

## Convolution and second moments {#section-convolution}

<p>For a real kernel $f$ with $\sum_x(1+|x|^2)|f(x)|<\infty$, write</p>
<div class="math-display">$$m(f)=\sum_xf(x),\quad b(f)=\sum_xxf(x),\quad S(f)=\sum_xxx^{\mathsf T}f(x),\quad M_2(f)=\sum_x|x|^2|f(x)|.$$</div>
<p>Thus $S(f)$ is a matrix and need not be positive when $f$ changes sign. Every entry is absolutely summable; the first moment is finite because $|x|\le1+|x|^2$.</p>
<a id="tag-QA8C" data-assertion="proposition" data-title="Absolute second moments justify the convolution moment identity"></a>
<p>If $f,g$ have the stated absolute moments, then $f*g$ does too, and</p>
<div class="math-display">$$\begin{aligned}
M_2(f*g)&\le2M_2(f)\|g\|_1+2\|f\|_1M_2(g),\\
S(f*g)&=m(g)S(f)+m(f)S(g)+b(f)b(g)^{\mathsf T}+b(g)b(f)^{\mathsf T}.
\end{aligned}$$</div>
<p>If both kernels are even, their first moments vanish and</p>
<div class="math-display">$$\sum_x|x|^2(f*g)(x)=m(g)\sum_x|x|^2f(x)+m(f)\sum_x|x|^2g(x).$$</div>
<p><em>Proof.</em> Use $|y+z|^2\le2|y|^2+2|z|^2$ in the nonnegative sum $\sum_{y,z}|y+z|^2|f(y)||g(z)|$. This proves the bound and justifies Fubini for every matrix entry. Expanding</p>
<div class="math-display">$$(y+z)(y+z)^{\mathsf T}=yy^{\mathsf T}+zz^{\mathsf T}+yz^{\mathsf T}+zy^{\mathsf T}$$</div>
<p>gives the matrix identity. Pairing $x$ with $-x$ gives $b(f)=b(g)=0$ for even kernels; taking the trace then gives the scalar identity. No product or difference of infinite moments occurs.</p>

## What a Fourier bound controls {#section-fourier}

<p>For an even real summable kernel, use $\widehat f(k)=\sum_xf(x)\cos(k\cdot x)$.</p>
<a id="tag-IVH2" data-assertion="proposition" data-title="Absolute moments give a quadratic Fourier expansion; nonnegative defects give the converse"></a>
<p>If $f$ is even and $M_2(f)<\infty$, then, as $k\to0$,</p>
<div class="math-display">$$\widehat f(0)-\widehat f(k)=\tfrac12 k^{\mathsf T}S(f)k+o(|k|^2),\qquad
|\widehat f(0)-\widehat f(k)|\le\tfrac12 |k|^2M_2(f).$$</div>
<p>Conversely, let $f\ge0$ be summable. If, for each coordinate $i$, there is $C_i\ge0$ such that</p>
<div class="math-display">$$\sum_x[1-\cos(t x_i)]f(x)\le C_i t^2$$</div>
<p>for all sufficiently small nonzero $t$, then $\sum_xx_i^2f(x)\le2C_i$ and $M_2(f)\le2\sum_iC_i$. In particular, for even nonnegative summable kernels, a quadratic Fourier defect near zero is equivalent to a finite second moment.</p>
<p><em>Proof.</em> The inequality $0\le1-\cos u\le u^2/2$ gives the bound. For the expansion, subtract $(k\cdot x)^2/2$ inside the sum. Divided by $|k|^2$, the summand tends to zero for each $x$ and is bounded in absolute value by $|x|^2|f(x)|$. Dominated convergence applies along every sequence $k\to0$, proving the full multivariable little-oh statement. For the converse, divide the nonnegative coordinate sum by $t^2$ and apply Fatou as $t\to0$. The pointwise limit is $x_i^2f(x)/2$. Sum the resulting bounds over the coordinates.</p>

## Why the sign matters {#section-signed-example}

<a id="tag-QKRD" data-assertion="proposition" data-title="A quadratic signed Fourier defect need not control the absolute second moment"></a>
<p>On $\mathbb Z$, set $f(0)=0$ and $f(n)=(-1)^{|n|}/|n|^3$ for $n\ne0$. This is an even summable kernel with $M_2(f)=\infty$, although</p>
<div class="math-display">$$\widehat f(0)-\widehat f(k)=-(\log2)k^2+O(k^4)\qquad(k\to0).$$</div>
<p><em>Proof.</em> The absolute second moment is $2\sum_{n\ge1}1/n$. To calculate the Fourier defect without differentiating a divergent series, first damp the coefficients by $r^{|n|}$, where $0<r<1$. The damped series is twice differentiable, and the logarithmic power series gives</p>
<div class="math-display">$$\widehat f_r''(k)=-2\sum_{n\ge1}\frac{(-r)^n\cos(nk)}n
=2\log|1+re^{ik}|.$$</div>
<p>On every closed interval inside $(-\pi,\pi)$, the right side converges uniformly to $2\log(2\cos(k/2))$. Also $\widehat f_r(0)\to\widehat f(0)$, $\widehat f_r'(0)=0$, and $\widehat f_r\to\widehat f$ uniformly. Integrating twice and passing to the limit therefore gives</p>
<div class="math-display">$$\widehat f(k)-\widehat f(0)=2\int_0^k(k-s)\log(2\cos(s/2))\,ds.$$</div>
<p>Since $\log(2\cos(s/2))=\log2+O(s^2)$ near zero, the claimed expansion follows. Adding a point mass at zero can prescribe the total mass without changing either the defect or the divergent absolute second moment.</p>
<p>This example concerns arbitrary signed kernels. It is not a counterexample to a percolation estimate. The manuscript's overview explicitly warns that its effective step kernel may have negative values; the nonnegative bounds on the individual lace coefficients are what allow the moment argument below.</p>

## The coefficient criterion and the effective quadratic term {#section-lace-moments}

<p>Let $D$ be the uniform nearest-neighbour step law, so $\widehat D(k)=d^{-1}\sum_i\cos k_i$ and $S(D)=I/d$.</p>
<a id="tag-22TW" data-assertion="corollary" data-title="Summable nonnegative coefficient bounds control the signed lace moment and dispersion"></a>
<p>Suppose $\pi_n\ge0$ are even kernels, $\sum_n\|\pi_n\|_1<\infty$, and there are $c_n\ge0$ with $C=\sum_nc_n<\infty$ such that</p>
<div class="math-display">$$\sum_x[1-\cos(k\cdot x)]\pi_n(x)\le c_n[1-\widehat D(k)]$$</div>
<p>for every $n$ and every $k$ in a neighbourhood of zero. Then $\Pi=\sum_n(-1)^n\pi_n$ satisfies</p>
<div class="math-display">$$\sum_n\sum_x|x|^2\pi_n(x)\le C,\qquad M_2(\Pi)\le C.$$</div>
<p>Assume further that $\Pi$ is invariant under coordinate reflections and permutations, and that $j>0$ satisfies $j(1+m(\Pi))=1$. For the signed kernel $Q=jD*(\delta_0+\Pi)$, put</p>
<div class="math-display">$$a=1+j\sum_x|x|^2\Pi(x).$$</div>
<p>Then $m(Q)=1$ and</p>
<div class="math-display">$$1-\widehat Q(k)=\frac a{2d}|k|^2+o(|k|^2).$$</div>
<p>If $a>0$, the denominator is nonzero for all sufficiently small nonzero $k$, and</p>
<div class="math-display">$$\frac1{1-\widehat Q(k)}\sim\frac{2d}{a|k|^2},\qquad
\frac{1+\widehat\Pi(k)}{1-\widehat Q(k)}\sim\frac{2d}{ja|k|^2}.$$</div>
<p>The sufficient condition $jC<1$ guarantees $a>0$.</p>
<p><em>Proof.</em> Set $k=t e_i$ in the coefficient bound. Since $1-\widehat D(t e_i)=(1-\cos t)/d$, Fatou as in IVH2 gives $\sum_xx_i^2\pi_n(x)\le c_n/d$. Summing over $i,n$ and using Tonelli proves the first bound; the triangle inequality proves the second.</p>
<p>QA8C gives absolute second-moment summability for $Q$ and</p>
<div class="math-display">$$S(Q)=j\left[\frac{1+m(\Pi)}d I+S(\Pi)\right].$$</div>
<p>Coordinate reflections make the off-diagonal entries of $S(\Pi)$ vanish, and coordinate permutations make its diagonal entries equal. Thus $S(Q)=aI/d$. IVH2 and $m(Q)=1$ give the expansion. If $a>0$, its error is smaller than half its leading quadratic term near zero, so both divisions are valid. The numerator of the second quotient tends to $1+m(\Pi)=1/j$. Finally, $a\ge1-jM_2(\Pi)\ge1-jC$.</p>
<p>For the lace coefficients, the mass hypothesis is supplied by <a href="/tag/3W22/">3W22</a> under its stated small-diagram criterion. The all-order frequency bounds used here remain a separate premise. Likewise, the second quotient is a two-point Fourier transform only where the lace representation has been justified; the argument does not infer a critical Fourier series from a pointwise spatial identity alone. The <a href="/coverage/sources/heydenreich-hofstad-2017-diagrams/">Chapter 7 map</a> records this scope. No new source erratum or compiled association is asserted.</p>
