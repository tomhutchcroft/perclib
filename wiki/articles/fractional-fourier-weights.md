---
{
  "id": "fractional-fourier-weights",
  "title": "Fractional weights in critical Fourier integrals",
  "subtitle": "Absolute coordinate powers and weighted convolutions",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "A symmetric-difference integral gives the Fourier density of an absolute noninteger coordinate weight. Local regularity of the critical quotient makes this integral converge in Lp below the power-counting threshold, and positive Fejer approximations identify the resulting weighted spatial convolutions.",
  "context": [
    "Real even kernels on $\\mathbb Z^d$, with $d>2$, and normalized Haar measure on $\\mathbb T^d$.",
    "The effective kernel may be signed; its Fourier denominator has an explicit quadratic gap.",
    "Critical two-point functions need not be summable. Fourier densities and their weighted versions are constructed as integrable functions."
  ],
  "related": ["fourier-spatial-moment-bridge", "planar-lace-moments", "planar-pointwise-lace", "higher-lace-moments"],
  "sourceIds": ["hara-nearest-neighbour-2008"],
  "aliases": ["fractional coordinate weights", "critical fractional Fourier derivatives", "noninteger weighted convolutions"],
  "prototypeUses": []
}
---

## A Fourier multiplier from symmetric differences {#section-multiplier}

<p>For a periodic function $A$ and a coordinate $j$, put</p>
<div class="math-display">$$\delta_{t,j}A(k)=A(k)-\frac{A(k+te_j)+A(k-te_j)}2.$$</div>
<p>Translations are taken on the torus. For $0<\sigma<2$, define the positive constant</p>
<div class="math-display">$$c_\sigma=\left[\int_0^\infty\frac{1-\cos t}{t^{1+\sigma}}\,dt\right]^{-1}.$$</div>
<p>The integral is finite: near zero its integrand is $O(t^{1-\sigma})$, and at infinity it is $O(t^{-1-\sigma})$.</p>

<a id="tag-AOKO" data-assertion="proposition" data-title="An integrable symmetric-difference multiplier gives the absolute fractional coordinate weight"></a>
<p>Let $1\le p<\infty$, let $A\in L^p(\mathbb T^d)$, and suppose that for some $\theta>\sigma$,</p>
<div class="math-display">$$\|\delta_{t,j}A\|_p\le C t^\theta\qquad(0<t\le1).$$</div>
<p>Then the following integral converges in $L^p$:</p>
<div class="math-display">$$\mathcal L_{j,\sigma}A
=c_\sigma\int_0^\infty\delta_{t,j}A\,\frac{dt}{t^{1+\sigma}}.$$</div>
<p>If $a(x)=\int e^{-ik\cdot x}A(k)\,dk$, its inverse Fourier coefficients are</p>
<div class="math-display">$$\int e^{-ik\cdot x}\mathcal L_{j,\sigma}A(k)\,dk
=|x_j|^\sigma a(x).$$</div>
<p><em>Proof.</em> Translation is continuous in $L^p$, so the integrand is strongly measurable. Its norm is integrable near zero by $\theta>\sigma$. For $t\ge1$, use $\|\delta_{t,j}A\|_p\le2\|A\|_p$. This proves convergence as a norm integral.</p>
<p>Taking an inverse Fourier coefficient is a bounded linear functional on $L^p$, since Haar measure has total mass one. It may therefore be interchanged with the norm integral. Translation multiplies that coefficient by $e^{\pm itx_j}$, and hence the result is</p>
<div class="math-display">$$c_\sigma a(x)\int_0^\infty\frac{1-\cos(tx_j)}{t^{1+\sigma}}\,dt
=|x_j|^\sigma a(x).$$</div>
<p>The last equality follows by a change of variable when $x_j\ne0$; both sides vanish when $x_j=0$. In particular, this multiplier gives an absolute weight, including when $\sigma=1$. An ordinary odd derivative would instead introduce the sign of $x_j$.</p>

## Fractional densities for a critical quotient {#section-quotient}

<p>Let $K\ge2$ be real, and suppose real even kernels $b,Q$ satisfy</p>
<div class="math-display">$$\sum_x(1+|x|^K)(|b(x)|+|Q(x)|)<\infty,\qquad
\sum_xQ(x)=1,\qquad F(k):=1-\widehat Q(k)\ge c|k|^2$$</div>
<p>on $[-\pi,\pi]^d$, with $c>0$. Set $R=\widehat b/F$ off zero and $\tau(x)=\int e^{-ik\cdot x}R(k)\,dk$. This integral exists for $d>2$.</p>
<p>Call a weight $s$ admissible if $0\le s<K$, or if $s=K$ and $K$ is an even integer. Define $g_{0,j}=\tau$ and $g_{s,j}(x)=|x_j|^s\tau(x)$ for $s>0$.</p>

<a id="tag-65QV" data-assertion="theorem" data-title="Absolute kernel moments give Lp Fourier densities for admissible real coordinate weights"></a>
<p>Let $s$ be admissible and let $1\le p<\infty$. If</p>
<div class="math-display">$$p(2+s)<d,$$</div>
<p>then there is $B_{s,j}\in L^p(\mathbb T^d)$ whose inverse Fourier coefficients are $g_{s,j}$. In particular, whenever $s<d-2$,</p>
<div class="math-display">$$|\tau(x)|\le C_s\langle x\rangle^{-s}.$$</div>
<p>Constants may depend on $K,s,p,d$, the moment bounds and the gap. No endpoint assertion is made when $p(2+s)=d$, or when $s=K$ is not an even integer.</p>
<p><em>Proof.</em> For an even integer $s$, take $B_{s,j}=i^{-s}\partial_j^sR$. The derivative bound and the inverse-coefficient identity are <a href="/tag/2ZOB/">2ZOB</a> and <a href="/tag/1165/">1165</a>. Their integer moment hypotheses hold because $s\le K$. At $s=0$, simply take $B_{0,j}=R$.</p>
<p>Otherwise write $s=m+\sigma$, where $m$ is a nonnegative even integer and $0<\sigma<2$. Put $A=i^{-m}\partial_j^mR$ and $a=m+2$. The integer derivative estimate gives $|A(k)|\le C|k|^{-a}$, so $A\in L^p$. We will prove</p>
<div class="math-display">$$\|\delta_{t,j}A\|_p\le C_\theta t^\theta
\quad\text{if}\quad 0<\theta\le\min\{2,K-m\},\qquad p(a+\theta)<d.$$</div>
<p>First record the local regularity needed for this estimate. If $K=n+\gamma$ with $n$ an integer and $0<\gamma<1$, the $n$th derivatives of $\widehat b,\widehat Q$ are $\gamma$-Hölder: use $|e^{iu}-1|\le C_\gamma|u|^\gamma$ in their absolutely convergent differentiated series. If $K$ is an integer, their derivatives through order $K$ are continuous and bounded.</p>
<p>On a ball of radius comparable to $r=|k|$ about a point close to zero, rescale coordinates by $r$. The functions $\widehat b$ and $F/r^2$ then have uniformly bounded derivatives through order $\lfloor K\rfloor$, and uniformly bounded highest Hölder seminorm when $K$ is noninteger. For $F/r^2$, the first two estimates follow from $F=O(r^2)$ and $\nabla F=O(r)$, using evenness and the absolute second moment. Higher derivative bounds carry factors $r^{\ell-2}$; the highest Hölder bound carries $r^{K-2}$. All these factors are bounded since $K\ge2$. The rescaled denominator is also bounded below by a positive constant.</p>
<p>Differentiating a reciprocal and taking differences therefore gives the same regularity bounds for $r^2R$. For the derivative $A$, Taylor's formula, with cancellation of the first-order term in the symmetric difference, yields</p>
<div class="math-display">$$|\delta_{t,j}A(k)|\le C t^\eta r^{-a-\eta},\qquad
\eta=\min\{2,K-m\},\qquad 0<t<r/4.$$</div>
<p>If $\eta\le1$, use the corresponding Hölder or first-derivative bound; if $1<\eta<2$, integrate the Hölder difference of the first derivative. Away from zero the same estimate holds with bounded constants in periodic coordinate charts.</p>
<p>For the $L^p$ bound, separate the balls of radius $5t$ around the singular points of $A(k)$ and $A(k\pm te_j)$. Their union has contribution to the norm at most $Ct^{d/p-a}$, by $pa<d$. On its complement, $t<r/4$, and for $\theta\le\eta$,</p>
<div class="math-display">$$|\delta_{t,j}A(k)|\le C t^\theta r^{-a-\theta}.$$</div>
<p>The latter power is $p$-integrable by the strict dimension condition. Since $d/p-a>\theta$, the near contribution is also $O(t^\theta)$. This proves the norm estimate for small $t$; boundedness of translations covers the remaining $t\le1$.</p>
<p>Now $s<K$ and $p(2+s)<d$ allow a choice</p>
<div class="math-display">$$\sigma<\theta<\min\{2,K-m,d/p-m-2\}.$$</div>
<p>Apply AOKO and set $B_{s,j}=\mathcal L_{j,\sigma}A$. By 1165 the inverse coefficients of $A$ are $x_j^m\tau(x)=|x_j|^m\tau(x)$, so the coefficients of $B_{s,j}$ are exactly $g_{s,j}$. This establishes the density without assuming a Fourier series for $g_{s,j}$.</p>
<p>For the spatial consequence choose $p=1$. The inverse integral bounds $|x_j|^s|\tau(x)|$ uniformly. For $x\ne0$, take a coordinate with $|x_j|\ge|x|/\sqrt d$; the unweighted inverse integral bounds the origin. Notice that the proof controls the fractional density in $L^p$. It does not assert a radial pointwise bound for that density, which can have additional directional singularities.</p>

## Real weights in critical convolution sums {#section-convolutions}

<a id="tag-ODMM" data-assertion="theorem" data-title="Weighted critical convolution identities hold for real admissible exponents below the power-counting threshold"></a>
<p>Under the preceding kernel assumptions, suppose additionally that $\tau(x)\ge0$. Let $\ell\ge2$, choose admissible weights $s_1,\ldots,s_\ell$ and coordinates $j_1,\ldots,j_\ell$, and assume</p>
<div class="math-display">$$2\ell+\sum_{r=1}^{\ell}s_r<d.$$</div>
<p>Then the nonnegative convolution sum is finite at every endpoint, uniformly in that endpoint, and</p>
<div class="math-display">$$(g_{s_1,j_1}*\cdots*g_{s_\ell,j_\ell})(y)
=\int e^{-ik\cdot y}\prod_{r=1}^{\ell}B_{s_r,j_r}(k)\,dk.$$</div>
<p>The same uniform finiteness holds if any coordinate weight is replaced by $|x|^{s_r}$, with weight one at $s_r=0$.</p>
<p><em>Proof.</em> Choose $p_r>1$ with $\sum_rp_r^{-1}=1$ and $p_r(2+s_r)<d$. Such a choice exists precisely because the displayed sum of singularity exponents is less than $d$. The preceding theorem puts each density in $L^{p_r}$, so their product belongs to $L^1$.</p>
<p>Smooth each density with the positive product Fejér kernel. Its spatial coefficients are $\vartheta_n(x)g_{s_r,j_r}(x)$, where</p>
<div class="math-display">$$\vartheta_n(x)=\prod_{i=1}^d\left(1-\frac{|x_i|}{n+1}\right)_+.$$</div>
<p>These coefficients are nonnegative, finitely supported and increase to $g_{s_r,j_r}$. The finite convolution identity and Hölder bound the smoothed spatial sum by $\prod_r\|B_{s_r,j_r}\|_{p_r}$, independently of $n$ and $y$. Monotone convergence gives finiteness and the same bound for the full convolution. Fejér approximation converges in each $L^{p_r}$; a telescoping product and Hölder give convergence of the products in $L^1$. Passing to the inverse integrals proves the identity. This is the argument of <a href="/tag/BNKQ/">BNKQ</a> with the fractional densities now supplied.</p>
<p>For $s>0$, $|x|^s\le C_{s,d}\sum_j|x_j|^s$. Expanding the finitely many coordinate choices proves the radial assertion. If $\tau_p\le\tau_c$, all these nonnegative spatial bounds for $\tau_c$ also hold uniformly for $\tau_p$, without comparing their fractional Fourier densities.</p>

## Application and source comparison {#section-source}

<p>For nearest-neighbour percolation in sufficiently large dimension, <a href="/tag/KF2I/">KF2I</a> gives $\sum_N\Pi_c^{(N)}(x)\le C_d\langle x\rangle^{-2(d-2)}$. Thus $b=\delta_0+\Pi_c$ and $Q=j_cD*b$ have finite absolute $K$th moments for every $K<d-4$. Their mass, symmetry and gap conditions come from <a href="/tag/F7N7/">F7N7</a>. For any real weights satisfying $2\ell+\sum_rs_r<d$, choose</p>
<div class="math-display">$$\max\{2,s_1,\ldots,s_\ell\}<K<d-4.$$</div>
<p>This is possible since $\ell\ge2$. ODMM therefore gives the corresponding weighted critical convolution identity and a uniform bound below criticality. This application uses the already completed qualitative spatial theorem; it does not improve its unspecified dimension threshold.</p>
<p>The comparison is with Hara's Lemma 4.2 and the fractional Fourier representations in Sections 4.1.3 and 4.3 of the <a href="https://www2.math.kyushu-u.ac.jp/~hara/papers/AOP_36_530.pdf">published paper</a>. The argument here uses a symmetric-difference norm integral and proves $L^p$ bounds directly. It does not reproduce the source's directional pointwise estimate (4.17), the sharper multidimensional middle-diagram estimates, or the endpoint at a non-even input moment. Those remain separate source correspondence questions. No new source erratum or Lean verification is asserted.</p>

## Integrated differences at the moment endpoint {#section-integrated-modulus}

<p>The endpoint left open above can be reached by retaining more of the absolute moment assumption. A pointwise Hölder estimate of order $\sigma$ would give a logarithmically divergent bound in AOKO. The absolute moment instead controls the required integral of differences directly.</p>
<p>For a summable kernel $a$, an integer $m\ge0$ and a coordinate $j$, define</p>
<div class="math-display">$$\begin{aligned}
\omega_{a,m,1}(t)&=\|\partial_j^m\widehat a(\,\cdot+te_j)-\partial_j^m\widehat a\|_\infty,\\
\omega_{a,m,2}(t)&=\|\delta_{t,j}\partial_j^m\widehat a\|_\infty.
\end{aligned}$$</div>

<a id="tag-2SC4" data-assertion="proposition" data-title="An absolute Fourier moment controls the integrated first or symmetric second difference at that exact order"></a>
<p>Let $\nu\in\{1,2\}$ and $0<\sigma<\nu$. If $\sum_x(1+|x_j|^{m+\sigma})|a(x)|<\infty$, then</p>
<div class="math-display">$$\int_0^\infty\omega_{a,m,\nu}(t)\,\frac{dt}{t^{1+\sigma}}
\le 2\left(\frac1\sigma+\frac1{\nu-\sigma}\right)
\sum_x|x_j|^{m+\sigma}|a(x)|.$$</div>
<p><em>Proof.</em> The differentiated Fourier series is absolutely convergent. The first difference has multiplier $e^{itx_j}-1$, and the symmetric difference has multiplier $1-\cos(tx_j)$. In either case, its absolute value is at most $2\min\{1,(t|x_j|)^\nu\}$. Taking the supremum inside the absolutely convergent sum and then using Tonelli reduces the claim to</p>
<div class="math-display">$$\int_0^\infty\min\{1,(tu)^\nu\}\,\frac{dt}{t^{1+\sigma}}
=u^\sigma\left(\frac1{\nu-\sigma}+\frac1\sigma\right)\qquad(u>0).$$</div>
<p>Split at $t=1/u$. When $u=0$, the integrand vanishes. No moment larger than $m+\sigma$ has been used.</p>

## The full input-moment endpoint {#section-endpoint}

<a id="tag-ENZ7" data-assertion="theorem" data-title="The exact real input moment gives the endpoint weighted Fourier density below the strict dimension threshold"></a>
<p>Under the kernel hypotheses of 65QV, let $K\ge2$ be any real number. If $1\le p<\infty$ and $p(2+K)<d$, then there is $B_{K,j}\in L^p(\mathbb T^d)$ whose inverse Fourier coefficients are $|x_j|^K\tau(x)$. Consequently, if $K<d-2$,</p>
<div class="math-display">$$|\tau(x)|\le C_K\langle x\rangle^{-K}.$$</div>
<p>If $\tau\ge0$, the convolution identity and radial finiteness conclusion of ODMM therefore hold for every $0\le s_r\le K$ satisfying $2\ell+\sum_rs_r<d$. The strict dimension inequalities are retained.</p>
<p><em>Proof.</em> Even integer $K$ is already covered by 65QV. Otherwise write $K=m+\sigma$, with $m\ge2$ even and $0<\sigma<2$, and put $A=i^{-m}\partial_j^mR$. Set</p>
<div class="math-display">$$\nu=\begin{cases}1,&0<\sigma<1,\\2,&1\le\sigma<2.\end{cases}$$</div>
<p>Thus $\sigma<\nu$ and $m-1+\nu\le K$. We will prove the norm integrability needed for the fractional multiplier, directly:</p>
<div class="math-display">$$\int_0^\infty\|\delta_{t,j}A\|_p\,\frac{dt}{t^{1+\sigma}}<\infty.$$</div>
<p>Write $D=\partial_j$. Differentiating $R=\widehat b/F$ and isolating the only terms containing an $m$th derivative gives</p>
<div class="math-display">$$D^mR=\frac{D^m\widehat b}{F}-\frac{\widehat b\,D^mF}{F^2}+E_m.
\tag{*}$$</div>
<p>Every numerator derivative in $E_m$ has order at most $m-1$. This follows from the product rule: the $D^m\widehat b$ term differentiates only the numerator, and the $D^mF$ term differentiates one denominator factor all $m$ times. All other distributions use lower derivatives. In particular, $D^qE_m$ for $q\le\nu$ requires derivatives of $b,Q$ of order at most $m-1+\nu\le K$.</p>
<p>Let $r$ be the distance to the singular frequency, truncated above at one. The moment and gap bounds give $D^hF=O(r^{2-h})$ and $D^h\widehat b=O(r^{-h})$ whenever the derivative in question is available. The first two bounds for $F$ use its mass and evenness. The product rule in the remainder of (*) then gives</p>
<div class="math-display">$$|D^qE_m(k)|\le C r^{-m-2-q}\qquad(0\le q\le\nu).$$</div>
<p>One can see the exponent term by term: a differentiated quotient term has the form $D^{h_0}\widehat b\,F^{-1-l}\prod_{u=1}^lD^{h_u}F$ with $h_0+\sum_uh_u=m+q$. Its bound has power $-h_0-2(1+l)+\sum_u(2-h_u)=-m-q-2$.</p>
<p>The coefficients $C_0=F^{-1}$ and $C_1=-\widehat bF^{-2}$ of the two distinguished terms satisfy</p>
<div class="math-display">$$|D^qC_0(k)|\le C r^{-2-q},\qquad
|D^qC_1(k)|\le C r^{-4-q}\qquad(0\le q\le2).$$</div>
<p>For $0<t<r/4$, apply a first product difference if $\nu=1$. If $\nu=2$, use the exact second-difference product identity: besides the two terms with a second difference on one factor, it has the products of the corresponding first differences. These cross terms require only $D^{m+1}\widehat b$ and $D^{m+1}F$, which exist because $K\ge m+1$ in this case. The bounds above and $D^mF=O(r^{2-m})$ yield</p>
<div class="math-display">$$|\delta_{t,j}A(k)|\le C\left[
r^{-2}\omega_{b,m,\nu}(t)+r^{-4}\omega_{Q,m,\nu}(t)
+t^\nu r^{-m-2-\nu}\right].$$</div>
<p>Here $D^mF=-D^m\widehat Q$. For $\nu=1$, the symmetric difference is bounded by the average of the two first differences, whose supremum norms agree. For $\nu=2$, for example, a first difference of $C_1$ is $O(tr^{-5})$ and one of $D^mF$ is $O(tr^{1-m})$; their product has the displayed remainder bound. Terms with both differences on $C_1$, and the terms involving $C_0$, obey the same bound. All estimates are valid in periodic charts away from zero as well.</p>
<p>Since $K>2$ in the case under consideration, $d>p(K+2)$ implies $d>4p$. Thus $r^{-2}$ and $r^{-4}$ belong to $L^p$. Choose</p>
<div class="math-display">$$\sigma<\theta<\min\{\nu,d/p-m-2\}.$$</div>
<p>As in 65QV, remove small balls around the three shifted singularities. On the complement, the last term in the pointwise bound is at most $Ct^\theta r^{-m-2-\theta}$, whose $L^p$ norm is $O(t^\theta)$. On the removed balls, the bound $|A(k)|\le Cr^{-m-2}$ gives an $L^p$ contribution $O(t^{d/p-m-2})=O(t^\theta)$. Hence</p>
<div class="math-display">$$\|\delta_{t,j}A\|_p\le C\left[
\omega_{b,m,\nu}(t)+\omega_{Q,m,\nu}(t)+t^\theta\right]
\qquad(0<t\le1).$$</div>
<p>Proposition 2SC4 makes the first two terms integrable against $t^{-1-\sigma}\,dt$, using exactly the assumed $K$th moments. The remainder is integrable because $\theta>\sigma$. For $t\ge1$, use $\|\delta_{t,j}A\|_p\le2\|A\|_p$.</p>
<p>We have proved norm integrability, rather than the stronger pointwise gain assumed in the statement of AOKO. Its coefficient-interchange argument now applies directly: the norm integral $B_{K,j}=c_\sigma\int_0^\infty\delta_{t,j}A\,dt/t^{1+\sigma}$ has inverse coefficients $|x_j|^\sigma x_j^m\tau(x)=|x_j|^K\tau(x)$. The integer coefficient identity for $A$ is justified by 1165, since $m+2<d$. This proves the endpoint density, including odd integer $K$.</p>
<p>Taking $p=1$ and choosing a largest coordinate gives the spatial bound. For the convolution conclusion, choose the same Hölder exponents as in ODMM. Use 65QV for weights below $K$ and the new endpoint density for a weight equal to $K$; the positive Fejér argument is unchanged.</p>

<p>The endpoint does not conceal a higher-moment assumption. For instance, for any non-even $K>2$, the nonnegative kernel</p>
<div class="math-display">$$b=\delta_0+\sum_{n\ge2}\frac{\delta_{ne_1}+\delta_{-ne_1}}{n^{K+1}(\log n)^2}$$</div>
<p>has a finite absolute $K$th moment and no finite $(K+\varepsilon)$th moment for any $\varepsilon>0$, by the integral test. Taking $Q$ to be the nearest-neighbour random-walk kernel gives the other hypotheses whenever $d>p(K+2)$. The endpoint conclusion therefore applies even in this situation.</p>

<p>This completes the input-moment endpoint omitted in the earlier sections. Hara's Section 4.1.4, especially the separation of highest derivatives in (4.23), addresses the same shortage of an additional integer derivative. The proof here keeps that algebraic separation but controls integrated differences in $L^p$. It does not claim the source's directional pointwise estimates, the equality case in power counting, a sharper percolation dimension threshold, or new Lean verification.</p>

## The unweighted middle integral {#section-middle-integral}

<p>The weighted middle diagram in Hara (1.17) can also be treated directly with the $L^p$ densities. Write $r(k)=\min\{1,\operatorname{dist}_{\mathbb T^d}(k,0)\}$ and put</p>
<div class="math-display">$$J_d(p)=\int_{\mathbb T^d}\int_{\mathbb T^d}
\frac{dk\,dl}{r(k)^4r(l)^4r(p-k)^2r(p+l)^2r(k+l)^2}.$$</div>
<p>All differences are taken on the torus, and Haar measure is normalized as before.</p>

<a id="tag-U7QM" data-assertion="proposition" data-title="The unweighted middle integral is bounded above dimension seven and has every finite integrability exponent in dimension seven"></a>
<p>If $d\ge8$, then $\sup_p J_d(p)<\infty$. If $d=7$, then, for every $\varepsilon>0$,</p>
<div class="math-display">$$J_7(p)\le C_\varepsilon r(p)^{-\varepsilon}\qquad(p\ne0).$$</div>
<p>Consequently $J_d\in L^q(\mathbb T^d)$ for every finite $q\ge1$ whenever $d\ge7$.</p>
<p><em>Proof.</em> Set $h(k)=r(k)^{-2}$ and $A_p(k)=r(k)^{-4}r(p-k)^{-2}$. Replacing $l$ by $-v$ gives</p>
<div class="math-display">$$J_d(p)=\int A_p(k)A_p(v)h(k-v)\,dk\,dv.
$$</div>
<p>Young's convolution inequality and Hölder imply</p>
<div class="math-display">$$J_d(p)\le\|A_p\|_a^2\|h\|_b,
\qquad 1<a<2,\qquad \frac2a+\frac1b=2.$$</div>
<p>These inequalities may first be applied to bounded truncations; monotone convergence gives the displayed estimate whenever the norms on its right are finite.</p>
<p>For $d\ge8$, choose $a=5/4$ and $b=5/2$. The function $h$ belongs to $L^b$ because $2b=5<d$. Hölder with exponents $3/2$ and $3$, followed by translation invariance, gives</p>
<div class="math-display">$$\|A_p\|_a^a
=\int r(k)^{-4a}r(p-k)^{-2a}\,dk
\le\left(\int r(k)^{-6a}\,dk\right)^{2/3}
\left(\int r(k)^{-6a}\,dk\right)^{1/3}<\infty.$$</div>
<p>The last integral is finite since $6a=15/2<d$, and its bound is independent of $p$.</p>
<p>For $d=7$, it suffices to treat $0<\varepsilon<1$. Choose</p>
<div class="math-display">$$a=\frac{14}{12-\varepsilon},\qquad b=\frac7{2+\varepsilon}.$$</div>
<p>Then $2/a+1/b=2$, $2b<7$, $4a<7$, $2a<7$, and $6a>7$. The elementary torus convolution estimate</p>
<div class="math-display">$$\int r(k)^{-\alpha}r(p-k)^{-\gamma}\,dk
\le C_{\alpha,\gamma,d}\,r(p)^{d-\alpha-\gamma}
\quad(0<\alpha,\gamma<d,\ \alpha+\gamma>d)$$</div>
<p>therefore gives $\|A_p\|_a^a\le C r(p)^{7-6a}$. For completeness, when $p$ is close to zero, split into the balls of radius $|p|/2$ about $0,p$, the rest of the ball of radius $2|p|$ about zero, and its complement. The first three pieces are bounded by $C|p|^{d-\alpha-\gamma}$. On the complement, $r(p-k)$ is comparable to $r(k)$; integrating the radial power from $2|p|$ to a fixed radius gives the same bound. Away from zero, the two singularities are separated and the integral is uniformly bounded.</p>
<p>It follows that $J_7(p)\le C r(p)^{14/a-12}=C r(p)^{-\varepsilon}$. Larger $\varepsilon$ follow from any smaller positive one, since $r\le1$. For each finite $q$, choose $\varepsilon q<7$ to obtain $J_7\in L^q$. No boundedness assertion at $d=7$ is needed.</p>

## A real-weighted middle diagram {#section-middle-diagram}

<p>Retain the kernel assumptions of 65QV with real input moment $K\ge2$, and assume $\tau\ge0$. For $0\le\beta\le K$, set $g_{\beta,j}(x)=|x_j|^\beta\tau(x)$, with weight one at $\beta=0$. Define the nonnegative sum</p>
<div class="math-display">$$\begin{aligned}
H_{\beta,j}(a,b)=\sum_{x,y,z,u,v\in\mathbb Z^d}
&\tau(z)\tau(u)\tau(x-u)g_{\beta,j}(x)\tau(y-x)\\
&\times\tau(v-u)\tau(z+a-v)\tau(y+b-v).
\end{aligned}$$</div>
<p>The letters $a,b$ in this display denote displacement vectors; the kernel $b$ in the critical quotient retains its earlier meaning.</p>

<a id="tag-5PWM" data-assertion="theorem" data-title="An integrable fractional density controls the weighted Hara middle diagram uniformly in both displacements"></a>
<p>If $d\ge7$ and $0\le\beta\le K$ with $\beta<d-2$, then $H_{\beta,j}(a,b)$ is finite uniformly in $a,b$. More precisely, choose any $1<p<d/(2+\beta)$ and let $B_{\beta,j}\in L^p$ be the density supplied by 65QV or ENZ7. Then</p>
<div class="math-display">$$\begin{aligned}
H_{\beta,j}(a,b)=\int_{(\mathbb T^d)^3}
&e^{-i(k\cdot a+l\cdot b)}B_{\beta,j}(q)R(k)^2R(l)^2\\
&\times R(q-k)R(q+l)R(k+l)\,dq\,dk\,dl,
\end{aligned}$$</div>
<p>the integral is absolutely convergent, and</p>
<div class="math-display">$$\sup_{a,b}H_{\beta,j}(a,b)
\le C\|B_{\beta,j}\|_p\|J_d\|_{p'}<\infty,
\qquad \frac1p+\frac1{p'}=1.$$</div>
<p>The same uniform finiteness holds with the radial weight $|x|^\beta$. If $0\le\tau_t\le\tau$ pointwise, it also holds uniformly for the corresponding diagrams with every factor replaced by $\tau_t$.</p>
<p><em>Proof.</em> The strict inequality $\beta<d-2$ permits the displayed choice of $p>1$. The weighted density exists by 65QV for $\beta<K$ and by ENZ7 for $\beta=K$. The quadratic gap and summable numerator give $|R(k)|\le C r(k)^{-2}$. Thus the absolute integral in the statement is bounded by</p>
<div class="math-display">$$C\int |B_{\beta,j}(q)|J_d(q)\,dq
\le C\|B_{\beta,j}\|_p\|J_d\|_{p'},$$</div>
<p>which is finite by U7QM. It remains to justify its equality with the spatial sum; the individual kernels need not be summable.</p>
<p>Let $P_t$ be the periodic heat kernel with Fourier multipliers $e^{-t|x|^2}$, and set $R_t=P_t*R$, $B_t=P_t*B_{\beta,j}$. Their inverse coefficients are</p>
<div class="math-display">$$\tau_t(x)=e^{-t|x|^2}\tau(x),\qquad
g_t(x)=e^{-t|x|^2}g_{\beta,j}(x).$$</div>
<p>They are nonnegative and summable, since the coefficients of an $L^1$ function are bounded. They increase to the original coefficients as $t\downarrow0$.</p>
<p>The heat smoothing has the useful uniform estimate</p>
<div class="math-display">$$|R_t(k)|\le C r(k)^{-2}\qquad(0<t\le1).$$</div>
<p>To see this, convolve the bound for $R$ with the positive heat kernel. Its periodized Gaussian representation first gives $P_t*r^{-2}\le Ct^{-1}$ by scaling near the singularity; the remaining periodic terms are bounded. This is sufficient when $r(k)\le2\sqrt t$. Otherwise split the Gaussian displacement at $r(k)/2$. In the inner part the power is at most $Cr(k)^{-2}$. In the outer part, factor off $e^{-c r(k)^2/t}$ and apply the same $Ct^{-1}$ bound to a Gaussian with twice the variance. Since $t^{-1}e^{-c r(k)^2/t}\le Cr(k)^{-2}$, the estimate follows. Constants may depend on $d$, but not on $t$.</p>
<p>For the smoothed kernels, write the eight Fourier factors in the order of the spatial definition, with frequencies $-k,k-q,-l-q,q,-l,k+l,k,l$. Evenness gives the product in the statement. Expanding their absolutely convergent series and integrating in $q,k,l$ imposes three equations on the eight edge displacements $s_1,\ldots,s_8$:</p>
<div class="math-display">$$s_4=s_2+s_3,\qquad
s_7=a+s_1-s_2-s_6,\qquad
s_8=b+s_3+s_5-s_6.$$</div>
<p>Their solutions are exactly $(z,u,x-u,x,y-x,v-u,z+a-v,y+b-v)$, with a unique choice of $x,y,z,u,v$. This proves the identity with unit multiplicity. Termwise integration is justified by the product of the eight finite $\ell^1$ norms, before any constraints are imposed.</p>
<p>We now pass to the limit in that identity. Heat convolution is an $L^p$ contraction and $B_t\to B_{\beta,j}$ in $L^p$. The uniform bound on the seven unmarked factors makes the contribution of $B_t-B_{\beta,j}$ at most $C\|B_t-B_{\beta,j}\|_p\|J_d\|_{p'}$, which tends to zero. With the marked factor fixed at $B_{\beta,j}$, the unmarked product converges almost everywhere to its unsmoothed value; it is dominated by the integrable majorant already proved. Dominated convergence therefore gives the claimed Fourier integral. On the spatial side, monotone convergence gives $H_{\beta,j}$, completing the identification and the bound.</p>
<p>For $\beta>0$, use $|x|^\beta\le C_{\beta,d}\sum_j|x_j|^\beta$ and sum the coordinate bounds. At $\beta=0$ no comparison is needed. Replacing the kernel by a smaller nonnegative one only decreases each summand, which proves the last assertion.</p>

<p>This supplies the middle-diagram integral in Hara (4.8), (4.14) and (4.20) by a direct $L^p$ argument. The dependence on the fractional density is explicit; its availability still requires the stated coefficient moments and Fourier gap. The source's directional bound (4.17), its other marked-diagram decompositions and numerical dimension range remain separate. The wider weight range here is an additional estimate, not an erratum to the source's sufficient conditions.</p>

## A directional bound for the fractional density {#section-directional}

<p>The same symmetric-difference formula also gives a pointwise bound, provided the input moment reaches the next integer. For a coordinate $j$, write</p>
<div class="math-display">$$r(k)=\min\{1,\operatorname{dist}_{\mathbb T^d}(k,0)\},\qquad
\rho_j(k)=\min\{1,\operatorname{dist}_{\mathbb T^{d-1}}(k_{\ne j},0)\}.$$</div>

<a id="tag-MAT0" data-assertion="theorem" data-title="Integer input moments give a directional pointwise bound for a noninteger absolute Fourier weight"></a>
<p>Under the kernel hypotheses of 65QV, let $s>0$ be noninteger, put $n=\lceil s\rceil$, and suppose $n\le K$ and $s+2<d$. Write $s=m+\sigma$, where $m$ is a nonnegative even integer and $0<\sigma<2$. The density $B_{s,j}$ has a representative satisfying</p>
<div class="math-display">$$|B_{s,j}(k)|\le
C r(k)^{-1-\sigma}\rho_j(k)^{-m-1}
\qquad(\rho_j(k)>0).$$</div>
<p>This majorant belongs to $L^p$ whenever $1\le p<\infty$ and $p(s+2)<d$. Moreover, put $\varepsilon=n-s\in(0,1)$ and $r_j(k)=\min\{1,\operatorname{dist}_{\mathbb T}(k_j,0)\}$. At points where $r_j,\rho_j>0$, the preceding bound implies</p>
<div class="math-display">$$|B_{s,j}(k)|\le
\frac{C}{r_j(k)^{1-\varepsilon}\rho_j(k)^n r(k)}.$$</div>
<p><em>Proof.</em> Put $A=i^{-m}\partial_j^mR$ and $\nu=n-m$. Since $s$ is not an integer, either $0<\sigma<\nu=1$ or $1<\sigma<\nu=2$. The derivative estimate 2ZOB applies through order $n$, because $\max\{2,n\}\le K$. In particular,</p>
<div class="math-display">$$|\partial_j^h A(k)|\le C r(k)^{-m-2-h}
\qquad(0\le h\le\nu).$$</div>
<p>Fix $k$ with $\rho_j(k)>0$. Its coordinate line avoids the singular frequency. For $0<t<r(k)/4$, a first-difference bound when $\nu=1$, or Taylor's formula with cancellation of the linear term when $\nu=2$, gives</p>
<div class="math-display">$$|\delta_{t,j}A(k)|\le C t^\nu r(k)^{-m-2-\nu}.$$</div>
<p>Integration against $t^{-1-\sigma}$ over this interval is therefore bounded by $Cr(k)^{-m-2-\sigma}$.</p>
<p>For the remaining shifts, the term $A(k)$ has the same bound after integration. For either shifted term, periodicity and the summability of the weights over successive periods give</p>
<div class="math-display">$$\int_{r(k)/4}^\infty |A(k\pm te_j)|\,\frac{dt}{t^{1+\sigma}}
\le C r(k)^{-1-\sigma}
\int_{-\pi}^{\pi}|A(u,k_{\ne j})|\,du.$$</div>
<p>Indeed, the first period has weight at most $(r(k)/4)^{-1-\sigma}$, and the sum of the maxima on all later periods is bounded by a constant depending on $\sigma$. The derivative estimate yields</p>
<div class="math-display">$$\int_{-\pi}^{\pi}|A(u,k_{\ne j})|\,du
\le C\int_{\mathbb R}(u^2+\rho_j(k)^2)^{-(m+2)/2}\,du+C
\le C\rho_j(k)^{-m-1}.$$</div>
<p>Since $\rho_j\le r$, this also dominates the earlier term $Cr^{-m-2-\sigma}$. The absolutely convergent pointwise integral $c_\sigma\int_0^\infty\delta_{t,j}A(k)\,dt/t^{1+\sigma}$ consequently has the first displayed bound. The $L^1$ norm-integral construction in 65QV applies because $s<n\le K$ and $s+2<d$. Fubini identifies the pointwise integral with that density almost everywhere. Thus no new inverse-coefficient assertion is needed at the excluded coordinate axis.</p>
<p>To check $L^p$ integrability, write $u=k_j$ and $\rho=|k_{\ne j}|$ near zero. Since $p(1+\sigma)>1$, integration in $u$ gives</p>
<div class="math-display">$$\int_{\mathbb R}(u^2+\rho^2)^{-p(1+\sigma)/2}\,du
=C_{p,\sigma}\rho^{1-p(1+\sigma)}.$$</div>
<p>After multiplying by $\rho^{-p(m+1)}$ and the transverse volume element, the remaining integral has power $\rho^{d-1-p(s+2)}$, which is integrable under the stated strict inequality. Away from zero but near the coordinate axis, only $\rho^{-p(m+1)}$ remains. It is integrable because $p(m+1)<d-1$, a consequence of $p(s+2)<d$ and $p(1+\sigma)>1$.</p>
<p>Finally, if $\nu=1$, the ratio of the first majorant to the second is $(r_j/r)^\sigma\le1$. If $\nu=2$, it is $\rho_j r_j^{\sigma-1}/r^\sigma\le1$. This proves the last assertion.</p>

<p>The last bound is the directional form of Hara (4.17), up to the harmless truncation of distances on the compact torus. Its proof here uses the symmetric-difference representation rather than the source's fractional integration kernels. The integer input condition $\lceil s\rceil\le K$ is essential to this argument: MAT0 makes no pointwise endpoint claim when a noninteger $s=K$ is the only available moment. ENZ7 still supplies its $L^p$ density in that case. No new source correction or numerical dimension threshold is asserted.</p>
