---
{
  "id": "tilted-fourier-bootstrap",
  "title": "Closing the tilted Fourier bootstrap",
  "subtitle": "Uniform coefficient moments up to the true mass",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "A symmetric diagram majorant and a complex Fourier estimate give uniform tilted coefficient moments. Continuity closes the bootstrap, proves the exponential correlation-length exponent in sufficiently large dimension, and identifies a simple pole.",
  "context": [
    "Nearest-neighbour bond percolation on $\\mathbb Z^d$, in sufficiently large dimension, with $p_c/2\\le p<p_c$ and $j=2dp$.",
    "$m=m(p)$ is the actual axial mass. Tilts initially satisfy $0\\le t<\\min\\{m,1\\}$.",
    "Constants are independent of p, t and d once the stated dimension threshold is met. No numerical threshold such as d>=11 is claimed."
  ],
  "related": ["tilted-susceptibility", "weighted-lace-coefficients", "bootstrap-diagram-bounds", "completed-fourier-bootstrap", "correlation-length-fourier"],
  "sourceIds": ["hara-correlation-1990", "heydenreich-hofstad"],
  "aliases": ["tilted lace coefficients", "exponential correlation-length exponent", "uniform tilt bootstrap"],
  "prototypeUses": []
}
---

## Transferring the diagram chain {#section-transfer}

<p>Write $\widehat D(k)=d^{-1}\sum_\nu\cos k_\nu$, $g=1-\widehat D$ and $C=g^{-1}$ away from zero. Integrals on the torus use normalized Haar measure. The complex tilted transform and its real part are</p>
<div class="math-display">$$T_t(k)=\sum_xe^{tx_1+ik\cdot x}\tau_p(x),\qquad
S_t(k)=\Re T_t(k)=\widehat\sigma_t(k),\qquad
\sigma_t(x)=\tau_p(x)\cosh(tx_1).$$</div>
<p>Interior exponential moments from <a href="/tag/OYWM/">OYWM</a> justify all differentiations and Fourier interchanges below. The real transform $S_t$ need not be nonnegative. Its absolute value will suffice.</p>

<p>Let $\Pi^{(N)}$ be the nonnegative coefficients of the existing expansion. In the kernels $A,B_1,B_2$ of <a href="/tag/SJIL/">SJIL</a>, replace $\tau$ by $\sigma=\sigma_t$ and $\widetilde\tau$ by $\widetilde\sigma=L*\sigma$, where</p>
<div class="math-display">$$J(x)=p\mathbf1_{\{x\sim0\}},\qquad L(x)=2J(x)\cosh(tx_1).$$</div>
<p>Call the resulting chain diagram $\mathcal D_N^\sigma(x)$. Put $\Delta=\sup_x\sigma^{*3}(x)$, $U=\sup_x(\sigma^{*2}*\widetilde\sigma)(x)$ and $r=2U\Delta$. These are new diagram quantities; they are not the unweighted diagrams.</p>
<a id="tag-IZDP" data-assertion="proposition" data-title="A symmetric majorant transfers all lace orders to tilted coordinate moments"></a>
<p>For $N\ge1$ and all $x$,</p>
<div class="math-display">$$\cosh(tx_1)\Pi^{(N)}(x)\le4^N\mathcal D_N^\sigma(x).$$</div>
<p>For a fixed coordinate $\mu$, let $w(x)=x_\mu^2$ and define</p>
<div class="math-display">$$W_0=\sum_xw(x)\widetilde\sigma(x)\sigma(x),\qquad
W=\sup_a\sum_xw(x)\widetilde\sigma(x)\sigma(x-a).$$</div>
<p>Let $H$ be the supremum of the diagram in <a href="/tag/09JN/">09JN</a>, with these replacement kernels and with its weight $h(t-u)$ replaced by $w(t-u)$. If these quantities are finite, the zeroth weighted coefficient is at most $W_0$, the first is at most $4[W_0+16U\Delta W]$, and, for $N\ge2$,</p>
<div class="math-display">$$\begin{aligned}
\sum_xw(x)\cosh(tx_1)\Pi^{(N)}(x)
\le4^N(2N+1)\bigl[&\Delta W\{2U+(1+\ell)N\Delta\}r^{N-1}\\
&+(N-1)\Delta^2(U^2W+H)r^{N-2}\bigr],\qquad \ell=\sum_xL(x).
\end{aligned}$$</div>
<p>The corresponding mass bounds are $U$ at order zero, $4U\Delta^2$ at order one and $4^N\Delta r^N$ for $N\ge1$.</p>
<p><em>Proof.</em> For real numbers $a_1,\ldots,a_q$,</p>
<div class="math-display">$$\cosh\!\left(\sum_i a_i\right)\le2^{q-1}\prod_i\cosh a_i.$$</div>
<p>Use the route of $2N+1$ displacements through the chain in 09JN. In either term of each intermediate kernel, every nonzero route displacement is an actual line of that diagram; the constrained displacement in the second term is zero. Multiplying the route factors by their coshes costs at most $2^{2N}$. Replace every remaining line by its larger symmetric majorant. For a connector,</p>
<div class="math-display">$$\cosh(tx_1)(J*\tau)(x)\le(2J\cosh(t\,\cdot_1))*\sigma(x)=\widetilde\sigma(x).$$</div>
<p>This proves the pointwise comparison, including the summation vertex in the second intermediate term. At order zero, double connection gives $\cosh(tx_1)\Pi^{(0)}(x)\le\sigma(x)^2$ off zero, and the coefficient vanishes at zero.</p>
<p>The first-step inequality gives $\sigma\le\delta_0+L*\sigma$, with $\sigma(0)=1$. Thus $w\sigma\le w\widetilde\sigma$. The proofs of SJIL, <a href="/tag/RZML/">RZML</a>, <a href="/tag/IT43/">IT43</a> and 09JN use only nonnegativity, evenness, this first-step comparison and the displayed diagram bounds. The displacement estimate becomes $(\sum_i x_{i,\mu})^2\le q\sum_i x_{i,\mu}^2$. The reversed sums are bounded by the supremum $\Delta$; Fourier positivity is not needed. In the refined first-order estimate, the actual initial triangle mass is $\sigma^{*3}(0)$, and its nontrivial part is at most $3U/2$, by the same two-nonzero-edges argument. Hence the stated estimates follow from those summations. Multiplication by $4^N$ gives the tilted bounds.</p>

## Estimates under a weak Fourier bound {#section-diagrams}

<a id="tag-VUY5" data-assertion="proposition" data-title="A weak tilted Fourier bound gives small all-order coefficient moments"></a>
<p>Fix $K\ge1$. Suppose, at the single tilt $t$,</p>
<div class="math-display">$$|T_t(k)|\le KC(k),\qquad
|\partial_\mu^2T_t(k)|\le\frac Kd C(k)^3\quad(k\ne0,\ 1\le\mu\le d).$$</div>
<p>There are constants $A_K,d_K<\infty$ such that, for $d\ge d_K$,</p>
<div class="math-display">$$\sum_{N\ge0}\sum_x\cosh(tx_1)\Pi^{(N)}(x)\le\frac{A_K}d,\qquad
\sum_{N\ge0}\sum_xx_\mu^2\cosh(tx_1)\Pi^{(N)}(x)\le\frac{A_K}{d^2}.$$</div>
<p><em>Proof.</em> The classical bootstrap supplies $1/2\le j\le2$ and $\tau_p(e)\le C_0/d$ for every nearest neighbour. In particular $\sigma(e)\le C_1/d$. The latter bound also follows by applying the first-step inequality twice and using the weighted walk integral in <a href="/tag/RD3X/">RD3X</a>. Here</p>
<div class="math-display">$$\widehat L(k)=2j\left[\widehat D(k)+\frac{\cosh t-1}{d}\cos k_1\right],\qquad
\ell\le8,\quad \sum_xx_\mu^2L(x)\le\frac8d.$$</div>
<p>RD3X therefore gives, for each fixed integer $s$ and all sufficiently large $d$,</p>
<div class="math-display">$$\int C^s\le c_s,\qquad
\int|\widehat L|^2C^s\le\frac{c_s}d,\qquad
\int|\widehat L|^2=\sum_xL(x)^2\le\frac{c}d.$$</div>
<p>Taking absolute values in Fourier inversion gives $\Delta\le K^3\int C^3$. Iterate $\sigma\le\delta_0+L*\sigma$ in the three factors to obtain</p>
<div class="math-display">$$L*\sigma^{*3}\le L+L^{*2}*\sigma+L^{*2}*\sigma^{*2}+L^{*2}*\sigma^{*3}.$$</div>
<p>The preceding integrals bound its supremum by $c_K/d$, so $U\le c_K/d$ and $r\le c_K/d$.</p>
<p>Since $\widetilde\sigma\le L+L^{*2}*\sigma$, the unshifted weighted pair satisfies</p>
<div class="math-display">$$W_0\le\frac{C_1}d\sum_xx_\mu^2L(x)
+\int|\partial_\mu^2S_t|\,|\widehat L|^2|S_t|
\le\frac{c_K}{d^2}.$$</div>
<p>For the shifted pair use $w(u+v)\le2w(u)+2w(v)$. Fourier inversion bounds the two resulting convolution suprema by</p>
<div class="math-display">$$W\le2\left(\sum_xw(x)L(x)\right)K^2\int C^2
+\frac{2K^2\ell}{d}\int C^4\le\frac{c_K}d.$$</div>
<p>It remains to retain the extra factor $d^{-1}$ in $H$. The Fourier identity in <a href="/tag/L1Y7/">L1Y7</a> holds with $\widehat L$ at each connector and $-\partial_\mu^2S_t$ at the marked line. Thus $H$ is at most $K^8/d$ times</p>
<div class="math-display">$$I=\int|\widehat L(k_1)\widehat L(k_2)|
C(k_1)^2C(k_2)^2C(k_3)^3
C(k_1-k_2)C(k_2-k_3)C(k_1-k_3)\,dk_1dk_2dk_3.$$</div>
<p>Cauchy–Schwarz separates the two connector factors. Their squared integral has square root $\int|\widehat L|^2$. The remaining squared product has total exponent twenty. Hölder, with exponents proportional to its six powers, bounds its integral by $\int C^{20}$: each individual frequency or difference is uniform under product Haar measure. Consequently</p>
<div class="math-display">$$I\le\left(\int|\widehat L|^2\right)\left(\int C^{20}\right)^{1/2}\le\frac cd,\qquad H\le\frac{c_K}{d^2}.$$</div>
<p>This deliberately uses only a sufficiently-large-dimension bound; $d>40$ makes this particular integral finite, and is not an asserted threshold for the theorem.</p>
<p>Insert $\Delta,\ell=O_K(1)$, $U,W=O_K(d^{-1})$ and $W_0,H=O_K(d^{-2})$ in the preceding proposition. Orders zero and one have coordinate moments $O_K(d^{-2})$. At order $N\ge2$, the two contributions are bounded by a polynomial in $N$ times $d^{-1}(c_K/d)^{N-1}$ and $d^{-2}(c_K/d)^{N-2}$, respectively, including the factor $4^N$ after enlarging $c_K$. Their sums are $O_K(d^{-2})$ once $d$ is large. The mass bounds sum to $O_K(d^{-1})$ in the same way. All sums are over the nonnegative coefficients before alternation.</p>

## Improving the complex transform {#section-improvement}

<a id="tag-X9O8" data-assertion="proposition" data-title="Small tilted coefficient moments improve the Fourier and second-derivative bounds with a universal constant"></a>
<p>There is an absolute constant $K_*\ge1$ with the following property. Suppose the signed kernel $\Pi=\sum_N(-1)^N\Pi^{(N)}$ satisfies</p>
<div class="math-display">$$\sum_x\cosh(tx_1)|\Pi(x)|\le\frac Ad,\qquad
\sum_xx_\mu^2\cosh(tx_1)|\Pi(x)|\le\frac A{d^2}\quad(1\le\mu\le d),$$</div>
<p>and its tilted convolution equation holds. If $d\ge16A$, then</p>
<div class="math-display">$$|T_t(k)|\le K_*C(k),\qquad
|\partial_\mu^2T_t(k)|\le\frac{K_*}{d}C(k)^3\quad(k\ne0).$$</div>
<p>The constant $K_*$ does not depend on $A$.</p>
<p><em>Proof.</em> Put $B_t(k)=1+\sum_xe^{tx_1+ik\cdot x}\Pi(x)$, $b=B_t(0)$ and</p>
<div class="math-display">$$D_t(k)=\frac1d\left[\cosh t\cos k_1+i\sinh t\sin k_1+\sum_{\nu>1}\cos k_\nu\right],\qquad
F_t=1-jD_tB_t.$$</div>
<p>The equation gives $F_tT_t=B_t$. At zero, $F_t(0)=b/\chi_p(te_1)>0$, since $b\ge1-A/d>0$.</p>
<p>Each coefficient is invariant under each coordinate reflection. Averaging those reflections and using $1-\cos(nx)\le n^2(1-\cos x)$ gives, with $\eta=A/d^2$,</p>
<div class="math-display">$$|b-\Re B_t(k)|\le\eta d\,g(k),\qquad
|\Im B_t(k)|\le t\eta|\sin k_1|.$$</div>
<p>For the second estimate, all sine terms except the first coordinate cancel. Use $|\sin(nk_1)|\le|n\sin k_1|$ and $|\sinh(tn)|\le t|n|\cosh(tn)$. The real estimate also uses $1-\prod_\nu c_\nu\le\sum_\nu(1-c_\nu)$ for $c_\nu\in[-1,1]$.</p>
<p>Writing $D_R=\Re D_t$ and $D_I=\Im D_t$, one has $D_t(0)-D_R\ge g$, $|D_R|\le2$ and $\sin^2 k_1\le2dg$. Hence</p>
<div class="math-display">$$\begin{aligned}
\Re F_t(k)-F_t(0)
&=j\{b[D_t(0)-D_R]+D_R[b-\Re B_t]+D_I\Im B_t\}\\
&\ge j[1-A/d-2\eta d-3\eta]g(k)\ge\frac j2g(k)\ge\frac14g(k).
\end{aligned}$$</div>
<p>Thus $F_t$ cannot vanish, $|B_t|\le2$ and $|T_t|\le8C$.</p>
<p>The integer-coordinate inequalities $|x_\mu|\le x_\mu^2$ give $|\partial_\mu B_t|,|\partial_\mu^2B_t|\le\eta$. Also $|D_t|\le2$ and its first two coordinate derivatives are at most $4/d$. With $j\le2$ and $\eta\le1/d$, these imply $|\partial_\mu F_t|\le20/d$ and $|\partial_\mu^2F_t|\le36/d$. Differentiate the quotient:</p>
<div class="math-display">$$\partial_\mu^2T_t=
\frac{\partial_\mu^2B_t}{F_t}
-\frac{2(\partial_\mu B_t)(\partial_\mu F_t)+B_t\partial_\mu^2F_t}{F_t^2}
+\frac{2B_t(\partial_\mu F_t)^2}{F_t^3}.$$</div>
<p>Using $|F_t|^{-1}\le4C$, $g\le2$ and $d\ge1$ bounds the right side by $K_*C^3/d$ with one absolute constant, for example $K_*=2^{18}$. The estimates use the complex denominator directly; positivity of a symmetrically tilted Fourier transform is never assumed.</p>

## Closing the tilt interval {#section-closure}

<a id="tag-1MCZ" data-assertion="theorem" data-title="All lace orders have uniform exponentially tilted coordinate moments up to the mass"></a>
<p>There are absolute $d_0,C_0<\infty$ such that, for $d\ge d_0$, $p_c/2\le p<p_c$, $0\le t\le\min\{m(p),1\}$ and every coordinate $\mu$,</p>
<div class="math-display">$$\sum_{N\ge0}\sum_x\cosh(tx_1)\Pi_p^{(N)}(x)\le\frac{C_0}d,\qquad
\sum_{N\ge0}\sum_xx_\mu^2\cosh(tx_1)\Pi_p^{(N)}(x)\le\frac{C_0}{d^2}.$$</div>
<p><em>Proof.</em> For fixed $p$, define on $0\le t<\min\{m,1\}$</p>
<div class="math-display">$$f(t)=\max\left\{1,\ \sup_{k\ne0}g(k)|T_t(k)|,\qquad
\max_\mu\sup_{k\ne0}d\,g(k)^3|\partial_\mu^2T_t(k)|\right\}.$$</div>
<p>The interior exponential majorant in OYWM makes the transforms and their second derivatives continuous in $t$, uniformly in $k$ on every compact tilt interval. The factors $g$ and $g^3$ are bounded and vanish at zero, so the suprema are finite and continuous.</p>
<p>At zero, <a href="/tag/6G0E/">6G0E</a> and the completed classical bootstrap give a total nonnegative coefficient mass $O(d^{-1})$ and total second moment $O(d^{-1})$. Coordinate permutation symmetry makes each coordinate moment $O(d^{-2})$. The improvement proposition therefore gives $f(0)\le K_*$ in sufficiently large dimension.</p>
<p>Fix $K=2K_*$. At any single tilt with $f(t)\le K$, the diagram proposition supplies the coefficient bounds with $A=A_K$. They give absolute convergence of the tilted signed series and justify weighting the existing spatial lace equation by Fubini. Increase $d_0$ so that $d\ge16A_K$. The improvement proposition then gives $f(t)\le K_*$. By continuity, $f$ cannot first reach $2K_*$ from its initial value at most $K_*$. Thus $f\le K_*$ on the whole open interval. Applying the diagram bound again gives a common $C_0=A_K$ there.</p>
<p>Each summand in the two displayed nonnegative series increases with $t\ge0$. Monotone convergence as $t$ approaches $\min\{m,1\}$ gives the endpoint estimates. No endpoint summability was used to obtain the improvement, and continuity was applied to the two-point transform, not to a coefficient series whose convergence was still in question.</p>

## The exponential correlation-length law {#section-length}

<a id="tag-OUHY" data-assertion="theorem" data-title="The true exponential correlation length has the mean-field scale and a simple tilted pole in sufficiently high dimension"></a>
<p>After increasing $d_0$, suppose $d\ge d_0$ and</p>
<div class="math-display">$$0<p_c-p\le\frac1{64d^2}.$$</div>
<p>Then $m=m(p)<1$, $\xi(p)=1/m(p)$, and</p>
<div class="math-display">$$\frac{m^2}{8d}\le\frac1{\chi(p)}\le\frac{2m^2}{d},\qquad
\frac1{16d^2(p_c-p)}\le\xi(p)^2\le\frac2{d^2(p_c-p)}.$$</div>
<p>In particular, for each fixed $d\ge d_0$, the exponential correlation-length exponent is $1/2$ in the bounded-ratio sense. Moreover, if $b_t=1+\sum_xe^{tx_1}\Pi_p(x)$ and $D_t=1+(\cosh t-1)/d$, then</p>
<div class="math-display">$$\lim_{t\uparrow m}(m-t)\chi_p(te_1)
=\frac{b_m}{j[(\sinh m/d)b_m+D_m b'_m]}
=\frac{d}{j\sinh m}\,[1+O(d^{-1})],$$</div>
<p>with a uniform relative error.</p>
<p><em>Proof.</em> Since $p_c\ge1/(2d)$, the stated interval lies above $p_c/2$. The reciprocal susceptibility estimate <a href="/tag/8ZGG/">8ZGG</a> gives $\chi(p)\ge32d$. Suppose $m\ge1$. The endpoint coefficient bounds at tilt one give $1/2\le b_0\le3/2$ and</p>
<div class="math-display">$$|b_1-b_0|\le\frac12\sum_xx_1^2\cosh(x_1)|\Pi_p(x)|\le\frac{C_0}{2d^2}.$$</div>
<p>Here $\cosh u-1\le u^2\cosh u/2$. For $d\ge8C_0$, $j\ge1/2$ and $D_1\le2$ imply</p>
<div class="math-display">$$j[(D_1-1)b_0+D_1(b_1-b_0)]\ge\frac1{16d}.$$</div>
<p>On the other hand, $F_0=b_0/\chi(p)\le3/(64d)$. Thus $F_1=1-jD_1b_1<0$. This contradicts $F_t=b_t/\chi_p(te_1)>0$ for $t<1$, by continuity of the coefficient sum at one. Therefore $m<1$.</p>
<p>The endpoint theorem now applies at $m$. It gives</p>
<div class="math-display">$$\sum_xe^{m|x_1|}|\Pi_p(x)|<\infty,\qquad
|b_m-b_0|\le\frac{C_0m^2}{2d^2}\le\frac{m^2}{16d}.$$</div>
<p>The first sum is at most twice its cosh-weighted counterpart. <a href="/tag/JQOQ/">JQOQ</a> supplies divergence at the true mass. All hypotheses of <a href="/tag/1BG0/">1BG0</a> are now satisfied, so its reciprocal bounds apply. The small-triangle estimate <a href="/tag/0Y4K/">0Y4K</a> and the classical bootstrap give $1/[2d(p_c-p)]\le\chi(p)\le1/[d(p_c-p)]$. Combining these inequalities proves the displayed bounds for $\xi^2$.</p>
<p>Finally, the endpoint coordinate moment gives the first absolute tilted moment and $|b'_m|\le mC_0/d^2$. The pole identity makes $b_m=(jD_m)^{-1}\ge1/4$. Hence, for large enough $d$, the positive-slope criterion of <a href="/tag/XZX4/">XZX4</a> holds. That proposition gives the exact residue. Dividing its denominator by $j b_m\sinh(m)/d$ bounds the relative correction by $O(d^{-1})$, since $m\le\sinh m$ and $D_m\le2$.</p>
<p>This completes the previously missing tilted estimates in the sufficiently-large-dimension classical regime. The <a href="/errata/heydenreich-hofstad/#mass-susceptibility-reciprocal">reciprocal correction</a> is now supported by a full written argument in that regime. The proof does not establish a numerical dimension threshold, the spread-out theorem or the manuscript's precise constants. No new Lean proof is claimed.</p>
