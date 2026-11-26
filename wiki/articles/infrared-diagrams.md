---
{
  "id": "infrared-diagrams",
  "title": "Random-walk bounds for infrared diagrams",
  "subtitle": "Uniform dimensions, shifted integrals and the zero-step term",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "Elementary walk estimates control Fourier diagrams under an explicit infrared-bound hypothesis. Spread-out triangles approach one; their nontrivial part tends to zero.",
  "context": [
    "Independent nearest-neighbour bond percolation on $\\mathbb Z^d$, unless a walk or a spread-out model is specified.",
    "All integrals on the torus use normalized Lebesgue measure.",
    "Statements about an infrared bound retain that bound as a hypothesis."
  ],
  "related": [
    "branching-random-walk",
    "connection-kernels",
    "triangle-susceptibility"
  ],
  "sourceIds": [
    "heydenreich-hofstad"
  ],
  "aliases": [],
  "prototypeUses": []
}
---

## The ordinary walk and its lazy version {#section-walk-threshold}

<p>Let $D(x)=(2d)^{-1}\mathbf1_{\{|x|_1=1\}}$, $a(k)=\widehat D(k)=d^{-1}\sum_j\cos k_j$, and $C_\lambda=\sum_{m\ge0}\lambda^mD^{*m}$ for $0\le\lambda\le1$. Write $\int f=\int_{[-\pi,\pi]^d}f(k)\,dk/(2\pi)^d$. For $\lambda<1$, $\widehat C_\lambda=(1-\lambda a)^{-1}$ and every discrete convolution below is absolutely summable.</p>

<a id="tag-KCOF" data-assertion="proposition" data-title="The simple random-walk triangle is finite exactly above dimension six"></a>
<p>For $j=1,2,3$, with nonnegative extended sums understood,</p>
<div class="math-display">$$C_1^{*j}(0)=\int(1-a(k))^{-j},\qquad
C_1^{*j}(0)<\infty\ \Longleftrightarrow\ d>2j.$$</div>
<p><em>Proof.</em> The lazy step law $D_{\mathrm{lazy}}=(\delta_0+D)/2$ has Green function</p>
<div class="math-display">$$G_{\mathrm{lazy}}(x)=\sum_{n\ge0}\sum_{m=0}^n2^{-n}\binom nmD^{*m}(x)=2C_1(x).$$</div>
<p>Tonelli applies, and $\sum_{n\ge m}2^{-n}\binom nm=2$, by the binomial generating series. The <a href="/tag/E9BP/">lazy-walk calculation</a> gives its convolution moments as the integrals of $[1-(1+a)/2]^{-j}$. Divide by $2^j$. The denominator is comparable to $|k|^2$ near zero and bounded below away from zero, so integrability is exactly $d>2j$. This avoids an invalid monotone-convergence argument in a Fourier variable where $a$ may be negative.</p>

## Uniform inverse moments and return counts {#section-walk-moments}

<a id="tag-RD3X" data-assertion="theorem" data-title="Dimension-uniform weighted random-walk integrals"></a>
<p>For each integer $n\ge0$, the integral $I_{d,n}=\int(1-a)^{-n}$ is bounded by a constant depending only on $n$ for every integer $d>2n$. For every pair of integers $l,n\ge0$, there is $K_{l,n}<\infty$ such that</p>
<div class="math-display">$$\int\frac{a(k)^{2l}}{(1-\lambda a(k))^n}\le K_{l,n}d^{-l}
\qquad(d>2n,\ 0\le\lambda\le1).$$</div>
<p><em>Proof.</em> If $K_1,\ldots,K_d$ are independent uniform angles and $X_j=1-\cos K_j$, then $I_{d,n}=\mathbb E[(d^{-1}\sum_jX_j)^{-n}]$. For $d+1$ samples, their full average is the average of the $d+1$ leave-one-out averages. Convexity of $x\mapsto x^{-n}$ and identical distribution give $I_{d+1,n}\le I_{d,n}$. The case $n=0$ is constant. For $n>0$, the first permitted dimension $2n+1$ has a finite integral: $1-\cos t\ge2t^2/\pi^2$ on $[-\pi,\pi]$, and the singularity is integrable in dimension greater than $2n$. Thus $I_{d,n}\le I_{2n+1,n}$.</p>
<p>For $d>4n$, Cauchy–Schwarz bounds the weighted integral at $\lambda=1$ by</p>
<div class="math-display">$$\left(\int a^{4l}\right)^{1/2}I_{d,2n}^{1/2}.$$</div>
<p>The first integral is the return probability after $4l$ steps. In a returning walk, the step positions can be paired so that the two steps in each pair are opposites. There are $(4l)!/[2^{2l}(2l)!]$ pairings. For any fixed pairing, independence makes its probability $(2d)^{-2l}$. A union bound therefore bounds the square root by a constant depending on $l$ times $d^{-l}$. For the finitely many dimensions $2n<d\le4n$, the integral is finite by $|a|\le1$ and the preceding integrability test; enlarge $K_{l,n}$ to include them. This proves the estimate at $\lambda=1$.</p>
<p>For $n\ge1$ and $\lambda<1$, expand the resolvent and integrate term by term, which is justified by absolute convergence:</p>
<div class="math-display">$$\int\frac{a^{2l}}{(1-\lambda a)^n}
=\sum_{m\ge0}\binom{m+n-1}{n-1}\lambda^mD^{*(2l+m)}(0)
=\bigl(D^{*2l}*C_\lambda^{*n}\bigr)(0).$$</div>
<p>The coefficients are nonnegative. The sum increases with $\lambda$, and its limit is the integral at one: on $a\ge0$ use monotone convergence, and on $a<0$ the integrand is bounded by one. The $n=0$ case has no parameter dependence. This proves the uniform damped estimate. The spatial expression is its value at zero, not its sum over all vertices; the <a href="/errata/heydenreich-hofstad/#walk-integral-zero-coefficient">corresponding manuscript correction</a> retains the claimed bound.</p>
<p>The trigonometric estimates used here follow from $1-\cos t=2\sin^2(t/2)$ and $2u/\pi\le\sin u\le u$ for $0\le u\le\pi/2$. The lower inequality is concavity above the chord, and the upper follows by integrating $\cos u\le1$.</p>

## Shifted triangles {#section-shifted}

<a id="tag-A9W9" data-assertion="proposition" data-title="Shifted walk triangles are bounded by the unshifted weighted triangle"></a>
<p>Put $c_\lambda(k)=(1-\lambda a(k))^{-1}$. For $d>6$, $0\le\lambda\le1$ and every torus vector $q$, both</p>
<div class="math-display">$$\int a(k)^2c_\lambda(k)^2\,
\frac{c_\lambda(k+q)+c_\lambda(k-q)}2$$</div>
<p>and</p>
<div class="math-display">$$\int a(k)^2c_\lambda(k)c_\lambda(k-q)c_\lambda(k+q)$$</div>
<p>are at most $\int a^2c_\lambda^3\le K_{1,3}/d$.</p>
<p><em>Proof.</em> First take $\lambda<1$. The inverse Fourier coefficients of $a^2c_\lambda^2$ are the nonnegative sequence $A=D^{*2}*C_\lambda^{*2}$. Thus</p>
<div class="math-display">$$\int a^2c_\lambda^2c_\lambda(\cdot+q)
=\sum_x A(x)C_\lambda(x)\cos(q\cdot x)
\le\sum_x A(x)C_\lambda(x)=\int a^2c_\lambda^3.$$</div>
<p>The other shift is identical. For the second integral, symmetry gives $c_\lambda(k\pm q)=U(k)\mp V(k)$, where</p>
<div class="math-display">$$U(k)=\sum_xC_\lambda(x)\cos(k\cdot x)\cos(q\cdot x),\qquad
V(k)=\sum_xC_\lambda(x)\sin(k\cdot x)\sin(q\cdot x).$$</div>
<p>Their product is $U^2-V^2\le U^2$. Multiply by the nonnegative weight $a^2c_\lambda$. Its inverse coefficients $B=D^{*2}*C_\lambda$ are nonnegative, so Fourier expansion yields</p>
<div class="math-display">$$\int a^2c_\lambda U^2
=\sum_{y,z}B(y+z)C_\lambda(y)C_\lambda(z)\cos(q\cdot y)\cos(q\cdot z)
\le\int a^2c_\lambda^3.$$</div>
<p>All series are absolutely convergent. Finally take $\lambda\uparrow1$. The two left integrands are nonnegative and converge away from finitely many singular points, so Fatou applies; RD3X gives convergence and the uniform bound on the right.</p>

## Consequences of an infrared bound {#section-infrared}

<a id="tag-ANZF" data-assertion="proposition" data-title="A uniform infrared bound controls critical triangles and open polygons"></a>
<p>Suppose nearest-neighbour percolation satisfies</p>
<div class="math-display">$$\widehat\tau_p(k)\le\frac A{1-a(k)}\qquad(p<p_c)$$</div>
<p>with $A<\infty$ independent of $p$. If $d>6$, then $\Delta_{p_c}(0)\le A^3 I_{d,3}<\infty$. If $d>12$, then</p>
<div class="math-display">$$\max_{e\sim0}\Delta_{p_c}(e)\le A^3\sqrt{\frac{I_{d,6}}{2d}}.$$</div>
<p>In particular, a common bound on $A$ over sufficiently large dimensions makes all neighbouring open triangles smaller than one. For every positive integer $s$ and every $p\le p_c$, one also has, as inequalities of nonnegative extended sums,</p>
<div class="math-display">$$\tau_p^{*s}(x)\le\tau_p^{*s}(0),\qquad
(D^{*2}*\tau_p^{*s})(x)\le(D^{*2}*\tau_p^{*s})(0).$$</div>
<p>These last two inequalities do not require the infrared hypothesis.</p>
<p><em>Proof.</em> Below $p_c$, sharpness gives finite susceptibility. <a href="/tag/F77A/">Cluster positivity and Fourier inversion</a> make $f=\widehat\tau_p$ nonnegative and identify $\Delta_p(0)=\int f^3$. The infrared hypothesis and RD3X give the first bound. Lattice symmetry gives the same value of $\Delta_p(e)$ for all neighbours, and therefore</p>
<div class="math-display">$$\Delta_p(e)=\int a f^3\le\left(\int a^2\right)^{1/2}\left(\int f^6\right)^{1/2}
\le A^3\sqrt{I_{d,6}/(2d)}.$$</div>
<p>Here $\int a^2=D^{*2}(0)=1/(2d)$. For the polygon inequalities, the Fourier transforms $f^s$ and $a^2f^s$ are nonnegative. Their inverse coefficient at $x$ is at most their zero coefficient, since $\cos(k\cdot x)\le1$.</p>
<p>Every fixed connection probability increases to its critical value as $p\uparrow p_c$: use finite path witnesses, finite-volume continuity, then exhaust the graph. Tonelli and monotone convergence pass every nonnegative spatial sum above to criticality, without asserting convergence of the critical Fourier series. The uniform dimension bound on $I_{d,6}$ proves the final smallness claim.</p>
<p>The infrared estimate itself remains a premise. Its lace-expansion proof and quantitative amplitude are separate obligations. No argument here transfers the walk estimate to percolation without that premise.</p>

## A wide step law {#section-spreadout}

<p>Let $L\ge1$ be an integer and $D_L(x)=(2L+1)^{-d}\mathbf1_{\{\|x\|_\infty\le L\}}$. This walk has a holding probability; the associated percolation graph has edges only between distinct vertices. Write $a_L=\widehat D_L$.</p>
<a id="tag-ZRVJ" data-assertion="theorem" data-title="Spread-out weighted diagrams are small and the full triangle tends to one"></a>
<p>For fixed $d$, there are $c_1,c_2>0$, independent of $L$, such that</p>
<div class="math-display">$$1-a_L(k)\ge c_1L^2|k|^2\quad(\|k\|_\infty\le L^{-1}),\qquad
1-a_L(k)\ge c_2\quad(\|k\|_\infty\ge L^{-1}).$$</div>
<p>For integers $l\ge1$, $n\ge0$ and $d>2n$,</p>
<div class="math-display">$$\int\frac{a_L^{2l}}{(1-a_L)^n}=O_{d,n}(L^{-d}).$$</div>
<p>For $d>6$, the full walk triangle satisfies</p>
<div class="math-display">$$\int(1-a_L)^{-3}=1+O_d(L^{-d}),\qquad \int(1-a_L)^{-3}\ge1.$$</div>
<p><em>Proof.</em> The transform factors as $a_L(k)=\prod_jh_L(k_j)$, where</p>
<div class="math-display">$$h_L(t)=\frac1{2L+1}\sum_{m=-L}^L\cos(mt)
=\frac{\sin((L+1/2)t)}{(2L+1)\sin(t/2)}.$$</div>
<p>When $|t|\le1/L$, every summand is at least $\cos1>0$, and</p>
<div class="math-display">$$1-h_L(t)\ge\frac{2L(L+1)}{3\pi^2}t^2.$$</div>
<p>All factors then lie in $[0,1]$, so $1-\prod_jh_L(k_j)\ge d^{-1}\sum_j(1-h_L(k_j))$. This proves the first bound.</p>
<p>For $2/L\le|t|\le\pi$, the sine formula and $\sin(|t|/2)\ge|t|/\pi$ give $|h_L(t)|\le\pi/4<1$. In the remaining range $1/L\le|t|\le2/L$, the indices $\lceil L/2\rceil\le|m|\le L$ occupy at least one third of the summands and satisfy $1/2\le|mt|\le2$. Thus $1-h_L(t)\ge(1-\cos(1/2))/3$, while every cosine is at least $\cos2$. These two bounds give $|h_L(t)|\le\rho<1$ uniformly in $L$. If any coordinate of $k$ is outside the small cube, $|a_L(k)|\le\rho$, proving the second bound.</p>
<p>Inside the cube, bound the numerator by one and change variables $q=Lk$:</p>
<div class="math-display">$$\int_{\|k\|_\infty\le L^{-1}}\frac{a_L^{2l}}{(1-a_L)^n}
\le C L^{-d}\int_{[-1,1]^d}|q|^{-2n}\,dq=O(L^{-d}).$$</div>
<p>Outside, the gap and $|a_L|^{2l}\le a_L^2$ bound the integral by $c_2^{-n}\int a_L^2=c_2^{-n}(2L+1)^{-d}$. This proves the weighted estimate.</p>
<p>For the full triangle, use the exact identity, valid for $-1\le t<1$,</p>
<div class="math-display">$$(1-t)^{-3}=1+3t+\frac{t^2(6-8t+3t^2)}{(1-t)^3}.$$</div>
<p>The polynomial in the numerator is nonnegative and bounded by 17 on this interval. Its integral remainder is $O(L^{-d})$ by the weighted estimate with $l=1,n=3$, and $\int a_L=D_L(0)=(2L+1)^{-d}$. This proves both claims, including the lower bound one. Equivalently the integral is the zero coefficient of the cubed Green function: damp first, expand in nonnegative return coefficients and then pass to one as in RD3X. It includes the zero-step term. The <a href="/errata/heydenreich-hofstad/#spreadout-triangle-baseline">manuscript's smallness conclusion</a> is therefore valid for the nontrivial part, not the full triangle.</p>
<p>For completeness, the spread-out percolation graph with $d\ge2$ has $0<p_c<1$. Its degree is $\Omega_L=(2L+1)^d-1$, so the simple-path count in <a href="/tag/NUJY/">NUJY</a> gives $p_c\ge1/(\Omega_L-1)>0$. It contains the planar nearest-neighbour graph, whose contour bound gives $p_c\le11/12$. This proves the nontriviality exercise without identifying the threshold.</p>
<p>The <a href="/coverage/sources/heydenreich-hofstad-2017-infrared/">Chapter 5 map</a> separates these walk and conditional percolation proofs from the remaining lace-expansion work. No new compiled Lean association is asserted.</p>

## Finite certificates for the sixth norms {#section-sixth-certificates}

<p>The qualitative constants in RD3X can be replaced by finite return sums and an explicit remainder. For the nearest-neighbour walk, put</p>
<div class="math-display">$$I_d=\int\frac{1}{(1-a)^6},\qquad
J_d=\int\frac{a^6}{(1-a)^6},\qquad p_{2m}(d)=D^{*2m}(0).$$</div>
<p>Let $N_{d,m}$ be the number of returning walks of length $2m$ in dimension $d$, so $p_{2m}(d)=N_{d,m}/(2d)^{2m}$. The initial values and recurrence are</p>
<div class="math-display">$$N_{0,0}=1,\quad N_{0,m}=0\ (m>0),\qquad
N_{d,m}=\sum_{k=0}^m\binom{2m}{2k}\binom{2k}{k}N_{d-1,m-k}.$$</div>

<a id="tag-LKS9" data-assertion="proposition" data-title="Finite return sums give explicit upper and lower bounds for the sixth random-walk norms"></a>
<p>For $d>12$,</p>
<div class="math-display">$$I_d=\sum_{m\ge0}\binom{2m+5}{5}p_{2m}(d),\qquad
J_d=\sum_{m\ge0}\binom{2m+5}{5}p_{2m+6}(d).$$</div>
<p>Both quantities are nonincreasing in the integer dimension $d$. If either series is truncated after $m=M\ge1$, its omitted tail is at most</p>
<div class="math-display">$$E_{d,M}=\frac8{15}
\left(\frac{\pi d}{16}\right)^{d/2}
\left(1+\frac{5}{2(M+1)}\right)^5
\frac{M^{6-d/2}}{d/2-6}.$$</div>
<p>Thus each finite partial sum is a lower bound, and adding $E_{d,M}$ gives an upper bound.</p>
<p><em>Proof.</em> In a returning walk, suppose $2k$ steps use the last coordinate. Choose their positions, then choose which $k$ are positive; the remaining steps form a returning walk in $d-1$ coordinates. This proves the recurrence. Expanding $(1-\lambda a)^{-6}$ for $\lambda<1$ and integrating gives the two series, because odd return probabilities vanish. As $\lambda\uparrow1$, the series increase termwise. The integrands are dominated by $(1-a)^{-6}$ on $a\ge0$ and by one on $a<0$. RD3X supplies integrability when $d>12$, so the limits give the displayed identities.</p>
<p>To bound a return probability, translate every torus coordinate by $\pi$, which sends $a$ to $-a$. For $m\ge1$,</p>
<div class="math-display">$$\begin{aligned}
p_{2m}(d)&=2\int_{a\ge0}a^{2m}
\le2\int\exp[-2m(1-a)]\\
&=2\left[\frac1{2\pi}\int_{-\pi}^{\pi}
\exp\!\left(-\frac{2m}{d}(1-\cos t)\right)\,dt\right]^d
\le2\left(\frac{\pi d}{16m}\right)^{d/2}.
\end{aligned}$$</div>
<p>The first inequality uses $u\le e^{u-1}$ for $0\le u\le1$. For the last, use $1-\cos t\ge2t^2/\pi^2$ and enlarge the one-dimensional Gaussian integral to the real line. For $m\ge M+1$,</p>
<div class="math-display">$$\binom{2m+5}{5}\le\frac{32m^5}{120}
\left(1+\frac{5}{2(M+1)}\right)^5,\qquad
\sum_{m=M+1}^{\infty}m^{5-d/2}\le\frac{M^{6-d/2}}{d/2-6}.$$</div>
<p>Multiplication proves the tail bound for $I_d$. Since $p_{2m+6}(d)=\int a^{2m+6}\le\int a^{2m}=p_{2m}(d)$, the same bound applies to $J_d$.</p>
<p>For dimension monotonicity, write $a$ as the average of $d$ independent variables distributed as the cosine of a uniform angle. The average of $d+1$ such variables is the average of their $d+1$ leave-one-out averages. Both functions used here are convex on $[-1,1)$: the second derivatives of $(1-t)^{-6}$ and $t^6(1-t)^{-6}$ are respectively</p>
<div class="math-display">$$\frac{42}{(1-t)^8},\qquad
\frac{6t^4(5+2t)}{(1-t)^8}.$$</div>
<p>Jensen's inequality and identical distribution of the leave-one-out averages therefore give $I_{d+1}\le I_d$ and $J_{d+1}\le J_d$.</p>

## An explicit connector-smallness test {#section-connector-certificate}

<p>Suppose the critical Fourier density satisfies $0\le R(k)\le A/(1-a(k))$, where $A\ge1$, and put $S=j_caR$. For the sixth norms used in <a href="/tag/FWHO/">FWHO</a>,</p>
<div class="math-display">$$U_6\le A I_d^{1/6},\qquad V_6\le j_cA J_d^{1/6},\qquad
\rho_6^6=(2U_6^5V_6)^6\le64j_c^6A^{36}I_d^5J_d.$$</div>
<p>Here $I_d\ge1$ by its zero-step term, so the bound on $U_6$ includes the maximum with one.</p>

<a id="tag-NI0W" data-assertion="corollary" data-title="Exact walk certificates turn explicit infrared amplitudes into sixth-norm connector smallness"></a>
<p>Each row below gives a sufficient condition: if $d\ge d_*$ and both $A,j_c\le c$, then $\rho_6$ is smaller than the last entry.</p>
<table>
<thead><tr><th>$d_*$</th><th>$c$</th><th>Upper bound for $I_{d_*}$</th><th>Upper bound for $J_{d_*}$</th><th>Upper bound for $\rho_6$</th></tr></thead>
<tbody>
<tr><td>$40$</td><td>$21/20$</td><td>$669/500$</td><td>$13589/100000000$</td><td>$407/500$</td></tr>
<tr><td>$64$</td><td>$11/10$</td><td>$1191/1000$</td><td>$387/20000000$</td><td>$37/50$</td></tr>
<tr><td>$100$</td><td>$23/20$</td><td>$279/250$</td><td>$363/100000000$</td><td>$181/250$</td></tr>
</tbody>
</table>
<p>Under the other critical hypotheses of FWHO, any one of these conditions therefore gives its Gaussian asymptotic, remainder exponent $4/(d+2)$, and weighted coefficient continuity for every $s<d-4$.</p>
<p><em>Proof.</em> Evaluate the two finite sums in LKS9 at $M=64$, using the integer recurrence through $m=67$. In its tail bound replace $\pi$ by $22/7$. This is a strict upper bound; for example, polynomial division and integration give $22/7-\pi=\int_0^1 t^4(1-t)^4/(1+t^2)\,dt>0$. All three displayed dimensions are even, so the resulting bound uses rational arithmetic only. The calculation below verifies that each partial sum plus this rational tail is below the displayed upper bound, and that</p>
<div class="math-display">$$64c^{42}\overline I^{\,5}\overline J<\overline\rho^{\,6}<1.$$</div>
<p>Dimension monotonicity and $j_c,A\le c$ then prove the assertion for every $d\ge d_*$. The consequence is FWHO with its smallness premise now supplied.</p>
<p>The table certifies the walk integrals and this implication. It does not establish the assumed percolation infrared amplitudes at dimensions 40, 64 or 100. F7N7 supplies such amplitudes in sufficiently large dimension, with an unspecified threshold. No numerical percolation threshold or source erratum is claimed here.</p>

<details><summary>Exact rational computation</summary>
<p>This is the complete standard-library Python certificate, also kept in <code>wiki/scripts/check-sixth-norms.py</code>. Every comparison uses integers and fractions; no numerical quadrature or floating-point estimate enters the certificate.</p>
<pre id="sixth-norm-certificate-code"><code>#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
&quot;&quot;&quot;Exact rational certificates for LKS9 and NI0W; no floating-point arithmetic.&quot;&quot;&quot;
from fractions import Fraction as F
from math import comb
import json

M = 64
rows = {
    40: (F(21, 20), F(669, 500), F(13589, 100000000), F(407, 500)),
    64: (F(11, 10), F(1191, 1000), F(387, 20000000), F(37, 50)),
    100: (F(23, 20), F(279, 250), F(363, 100000000), F(181, 250)),
}
weights = [
    [comb(2*m, 2*k) * comb(2*k, k) for k in range(m+1)]
    for m in range(M+4)
]
counts = [1] + [0] * (M+3)
certificates = []
for d in range(1, max(rows)+1):
    counts = [
        sum(weights[m][k] * counts[m-k] for k in range(m+1))
        for m in range(M+4)
    ]
    if d in (1, 2):
        assert all(counts[m] == comb(2*m, m)**d for m in range(M+4))
    if d not in rows:
        continue
    p = [F(counts[m], (2*d)**(2*m)) for m in range(M+4)]
    partial_I = sum(F(comb(2*m+5, 5)) * p[m] for m in range(M+1))
    partial_J = sum(F(comb(2*m+5, 5)) * p[m+3] for m in range(M+1))
    # LKS9, with the strict rational upper bound pi &lt; 22/7.
    tail = (F(8, 15) * F(22*d, 7*16)**(d//2)
            * (1 + F(5, 2*(M+1)))**5
            * F(M)**(6-d//2) / F(d//2-6))
    c, upper_I, upper_J, upper_rho = rows[d]
    assert d % 2 == 0 and d &gt; 12
    assert partial_I + tail &lt; upper_I
    assert partial_J + tail &lt; upper_J
    assert 64 * c**42 * upper_I**5 * upper_J &lt; upper_rho**6 &lt; 1
    certificates.append({
        &quot;dimension_at_least&quot;: d, &quot;amplitude_and_j_at_most&quot;: str(c),
        &quot;I_upper&quot;: str(upper_I), &quot;J_upper&quot;: str(upper_J),
        &quot;rho_upper&quot;: str(upper_rho), &quot;result&quot;: &quot;passed&quot;,
    })
print(json.dumps({&quot;cutoff&quot;: M, &quot;arithmetic&quot;: &quot;exact rational&quot;,
                  &quot;certificates&quot;: certificates}, indent=2))
</code></pre>
</details>

<p>The later <a href="/tag/7GNW/">explicit bootstrap calculation</a> proves the required percolation bounds for every $d\ge10^{11}$ and supplies all the other hypotheses of FWHO there. This coarse unconditional dimension bound leaves the premises at dimensions 40, 64 and100 unresolved.</p>


## Spatial diagrams with logarithmic corrections {#section-spatial-log-diagrams}

<p>The spatial decay of a kernel determines both the dimension threshold and the borderline logarithm. The following estimate treats the bubble and triangle together, including the configurations in which two vertices are close to each other.</p>

<a id="tag-GZCA" data-assertion="theorem" data-title="Two-sided spatial power and logarithmic bounds determine truncated bubbles and triangles"></a>
<p>Let $d\ge1$ be an integer, $0&lt;\alpha&lt;d$, and $a\in\mathbb R$. Suppose $f:\mathbb Z^d\to(0,\infty)$ satisfies, for some $0&lt;c\le C&lt;\infty$,</p>
<div class="math-display">$$
c\rho(x)^{\alpha-d}(1+\log\rho(x))^a
\le f(x)\le
C\rho(x)^{\alpha-d}(1+\log\rho(x))^a,
\qquad \rho(x)=1+\|x\|_\infty.
$$</div>
<p>No symmetry or Fourier-positivity assumption is made. For $R\ge2$ define</p>
<div class="math-display">$$
D_2(R)=\sum_{\|x\|_\infty\le R}f(x)^2,\qquad
D_3(R)=\sum_{\|x\|_\infty,\|y\|_\infty\le R}
f(x)f(y-x)f(y).
$$</div>
<p>For $m=2,3$, put $q=m\alpha-d$ and $b=ma$, and write $L_R=1+\log R$. Then</p>
<div class="math-display">$$
D_m(R)\asymp
\begin{cases}
R^qL_R^b,&q&gt;0,\\
L_R^{b+1},&q=0,\ b&gt;-1,\\
1+\log L_R,&q=0,\ b=-1,\\
1,&q&lt;0\ \text{or}\ (q=0,\ b&lt;-1).
\end{cases}
$$</div>
<p>The constants may depend on $d,\alpha,a,c,C$, but not on $R$. In particular, the full diagram $D_m(\infty)$ is finite exactly when $q&lt;0$, or when $q=0$ and $b&lt;-1$. In those finite cases its omitted tail satisfies</p>
<div class="math-display">$$
D_m(\infty)-D_m(R)\asymp
\begin{cases}
R^qL_R^b,&q&lt;0,\\
L_R^{b+1},&q=0,\ b&lt;-1.
\end{cases}
$$</div>

<p><em>Proof.</em> On a dyadic lattice annulus of radius $2^j$, $f$ is comparable to $2^{(\alpha-d)j}(1+j)^a$, and that annulus contains a number of vertices comparable to $2^{dj}$. Thus the bubble contribution there is comparable to</p>
<div class="math-display">$$2^{(2\alpha-d)j}(1+j)^{2a}.$$</div>
<p>We also need the ball-mass bound</p>
<div class="math-display">$$
\sum_{\|z\|_\infty\le2R}f(z)\le C_1R^\alpha L_R^a.
$$</div>
<p>Indeed, dyadic summation reduces it to $\sum_{k=0}^J2^{\alpha k}(1+k)^a\le C_2 2^{\alpha J}(1+J)^a$. After putting $u=J-k$, the ratio to the last term is bounded by the convergent series $\sum_{u\ge0}2^{-\alpha u}(1+u)^{|a|}$. This uses $\alpha&gt;0$ and holds for negative $a$ as well.</p>
<p>For the triangle, take a dyadic $R=2^j\ge8$ and restrict to</p>
<div class="math-display">$$
R/2&lt;\max\{\|x\|_\infty,\|y\|_\infty\}\le R.
$$</div>
<p>Among the three side lengths $\|x\|_\infty$, $\|y\|_\infty$, $\|y-x\|_\infty$, the largest exceeds $R/2$, and the second largest is at least half the largest. The two corresponding factors of $f$ are therefore at most $C_3R^{\alpha-d}L_R^a$. Partition the pairs according to which side is shortest, breaking ties arbitrarily. For each fixed shortest-side vector there are at most $C_dR^d$ choices of the remaining vertex, and that vector has norm at most $2R$. The shell contribution is consequently at most</p>
<div class="math-display">$$
3C_dR^d\bigl(C_3R^{\alpha-d}L_R^a\bigr)^2
\sum_{\|z\|_\infty\le2R}f(z)
\le C_4R^{3\alpha-d}L_R^{3a}.
$$</div>
<p>This includes a zero shortest side and does not bound all three sides below by a multiple of $R$.</p>
<p>For the matching lower bound, take $x_1\in[3R/4,R]$, $y_1\in[-R,-3R/4]$, and all other coordinates of both vertices in $[0,R/8]$. These boxes give at least $c_dR^{2d}$ pairs. They lie in the specified shell, and all three side lengths are between fixed positive multiples of $R$. Each product is therefore at least $c_1R^{3(\alpha-d)}L_R^{3a}$. The triangle shell has the asserted order.</p>
<p>After absorbing the finitely many smaller shells, both cases reduce to</p>
<div class="math-display">$$
D_m(R)\asymp
1+\sum_{j=1}^{\lfloor\log_2R\rfloor}
2^{qj}(1+j)^b.
$$</div>
<p>For non-dyadic $R$, squeeze between the adjacent dyadic radii; the displayed sums at those radii are comparable. If $q&gt;0$, the sum is comparable to its last term, since exponential growth absorbs every fixed power of $j$. If $q&lt;0$, the series converges and its tail is comparable to its first omitted term. At $q=0$, comparison with the integral of $(1+t)^b$ gives all three possibilities, including $\log(1+\log R)$ when $b=-1$. In the convergent borderline case the same integral gives the omitted tail. Monotonicity and the nonnegative shell decomposition justify passage to the full diagrams. $\square$</p>

## Bubble and triangle thresholds at dimensions four and six {#section-marginal-diagrams}

<a id="tag-9ZD3" data-assertion="corollary" data-title="Logarithmic spatial corrections separate bubble and triangle finiteness at the marginal dimensions"></a>
<p>Suppose a translation-invariant lattice two-point function satisfies the two-sided spatial bound</p>
<div class="math-display">$$
\tau(x)\asymp(1+\|x\|_\infty)^{2-d}
\bigl(1+\log(1+\|x\|_\infty)\bigr)^a
\qquad(d&gt;2).
$$</div>
<p>Define its truncated bubble $B(R)$ and triangle $T(R)$ by $D_2(R)$ and $D_3(R)$ above. In dimension six, the bubble is finite for every fixed $a$, with</p>
<div class="math-display">$$B(\infty)-B(R)\asymp R^{-2}L_R^{2a},$$</div>
<p>whereas the triangle is finite exactly when $a&lt;-1/3$. More precisely,</p>
<div class="math-display">$$
T(R)\asymp
\begin{cases}
L_R^{3a+1},&a&gt;-1/3,\\
1+\log L_R,&a=-1/3,\\
1,&a&lt;-1/3.
\end{cases}
$$</div>
<p>In the last case $T(\infty)-T(R)\asymp L_R^{3a+1}$. In dimension four, the bubble is finite exactly when $a&lt;-1/2$; its divergent cases have orders $L_R^{2a+1}$ for $a&gt;-1/2$ and $1+\log L_R$ for $a=-1/2$. The triangle always diverges there, with</p>
<div class="math-display">$$T(R)\asymp R^2L_R^{3a}.$$</div>
<p><em>Proof.</em> Apply GZCA with $\alpha=2$. For $d=6$, the bubble has $q=-2$, while the triangle has $q=0$ and $b=3a$. For $d=4$, the bubble has $q=0$ and $b=2a$, while the triangle has $q=2$. These substitutions give the claims. $\square$</p>
<p>With no logarithmic correction ($a=0$), the six-dimensional bubble is finite and the triangle grows like $\log R$. Thus bubble finiteness does not supply the finite-triangle hypothesis in the incipient-cluster or susceptibility results. All conclusions here are conditional on the displayed spatial bounds: this calculation does not determine a logarithmic exponent for a percolation model or furnish a reverse-BK estimate. A one-sided upper bound supplies only the corresponding diagram upper bounds; divergence requires a lower bound.</p>


## Local Fourier remainders {#section-local-fourier-remainder}

<p>In this section $|\cdot|$ is the Euclidean norm. For functions on $\mathbb R^d$ use the inverse transform $\mathcal F^{-1}h(x)=(2\pi)^{-d}\int e^{ik\cdot x}h(k)\,dk$. Homogeneous symbols which are not integrable at infinity are interpreted as tempered distributions; the formulas below concern their ordinary smooth inverse transforms away from the origin.</p>

<a id="tag-C5GY" data-assertion="proposition" data-title="A local symbol of order beta has an inverse transform of order minus d minus beta"></a>
<p>Let $\beta&gt;-d$, let $N$ be an integer with $N&gt;d+\beta$, and suppose $h$ is supported in $\{|k|\le1\}$, is $C^N$ away from zero, and satisfies</p>
<div class="math-display">$$
|\partial^\alpha h(k)|\le C_\alpha |k|^{\beta-|\alpha|}
\qquad(0&lt;|k|\le1,\ |\alpha|\le N).
$$</div>
<p>Then $h\in L^1(\mathbb R^d)$ and</p>
<div class="math-display">$$
|\mathcal F^{-1}h(x)|\le C(1+|x|)^{-d-\beta}.
$$</div>
<p>Also, let $H$ be smooth away from zero and homogeneous of degree $\beta&gt;-d$, and let $\chi$ be smooth, compactly supported and equal to one near zero. For every $M&gt;0$, away from the origin,</p>
<div class="math-display">$$
\mathcal F^{-1}(\chi H)(x)
=\mathcal F^{-1}H(x)+O_M(|x|^{-M})
\qquad(|x|\ge1),
$$</div>
<p>whenever the full inverse on the right is represented there by a smooth function.</p>
<p><em>Proof.</em> A smooth dyadic partition separates $h$ into annular pieces $h_j$ with $|k|\asymp r_j=2^{-j}$. The pieces meeting the outer boundary are covered by the same estimates after adjusting the constant. The derivative assumptions and the derivatives of the partition give</p>
<div class="math-display">$$
\|h_j\|_1\le Cr_j^{d+\beta},\qquad
\|\partial_\ell^N h_j\|_1\le Cr_j^{d+\beta-N}.
$$</div>
<p>For $x\ne0$, choose $\ell$ with $|x_\ell|\ge|x|/\sqrt d$ and integrate by parts $N$ times. The direct and integrated bounds together give</p>
<div class="math-display">$$
|\mathcal F^{-1}h_j(x)|
\le Cr_j^{d+\beta}\min\{1,(r_j|x|)^{-N}\}.
$$</div>
<p>For $|x|\ge1$, sum separately over $r_j\le|x|^{-1}$ and $r_j&gt;|x|^{-1}$. Both are geometric sums of order $|x|^{-d-\beta}$, since $d+\beta&gt;0$ and $N&gt;d+\beta$. The $L^1$ bound covers smaller $x$ and justifies summing the inverse transforms.</p>
<p>For the cutoff assertion put $B=(1-\chi)H$. It is smooth everywhere and has polynomial growth. If $n&gt;d+\beta$, then each $\partial_\ell^n B$ is integrable: it vanishes near zero and is $O(|k|^{\beta-n})$ at infinity. The distributional differentiation identity represents $\mathcal F^{-1}B$ on $x_\ell\ne0$ by $(-ix_\ell)^{-n}\mathcal F^{-1}(\partial_\ell^nB)$, and hence bounds it by $C_n|x_\ell|^{-n}$. Choose a largest coordinate of $x$ and then choose $n\ge M$, increasing it to meet the integrability condition. Subtract this rapidly decreasing function from the full inverse of $H$. $\square$</p>

## The first directional correction to the walk Green function {#section-walk-green-correction}

<a id="tag-IY26" data-assertion="theorem" data-title="The nearest-neighbour Green function has an explicit fourth-degree angular correction"></a>
<p>Let $d\ge3$ be an integer and $G(x)=\sum_{n\ge0}D^{*n}(x)$ for the ordinary nearest-neighbour walk defined above. Put</p>
<div class="math-display">$$
A_d=\frac{d\,\Gamma(d/2-1)}{2\pi^{d/2}},\qquad
Y_4(\theta)=\sum_{i=1}^d\theta_i^4-\frac3{d+2}
\quad(|\theta|=1).
$$</div>
<p>Uniformly over nonzero lattice points as $r=|x|\to\infty$,</p>
<div class="math-display">$$
G(x)=A_dr^{2-d}
+A_d\frac{d(d-2)(d+2)}{24}\,r^{-d}Y_4(x/r)
+O_d(r^{-d-2}).
$$</div>
<p>The polynomial $|x|^4Y_4(x/|x|)=\sum_i x_i^4-3|x|^4/(d+2)$ is homogeneous and harmonic of degree four. Thus the first correction is directional, despite all the coordinate symmetries of the walk.</p>
<p><em>Proof.</em> Write $q(k)=1-d^{-1}\sum_i\cos k_i$. For $0\le\lambda&lt;1$, Fourier inversion of the absolutely summable damped walk series gives $\sum_n\lambda^nD^{*n}(x)=\int e^{ik\cdot x}(1-\lambda\widehat D(k))^{-1}\,dk/(2\pi)^d$. On $\widehat D\ge0$ the integrand in absolute value is bounded by $q^{-1}$; on $\widehat D&lt;0$ it is bounded by one. Since $q(k)\asymp|k|^2$ near its only zero on the torus, this is integrable for $d&gt;2$. Dominated convergence on the Fourier side and monotone convergence of the nonnegative walk series give</p>
<div class="math-display">$$
G(x)=\int_{[-\pi,\pi]^d}\frac{e^{ik\cdot x}}{q(k)}\,\frac{dk}{(2\pi)^d}.
$$</div>
<p>Choose $\chi\in C_c^\infty(\mathbb R^d)$ supported in a ball of radius less than one inside $(-\pi,\pi)^d$ and equal to one near zero. Taylor expansion of the cosine and inversion of its leading quadratic term give</p>
<div class="math-display">$$
\frac1{q(k)}
=\frac{2d}{|k|^2}
+\frac d6\frac{\sum_i k_i^4}{|k|^4}+R(k),
\qquad
|\partial^\alpha R(k)|\le C_\alpha |k|^{2-|\alpha|}
$$</div>
<p>near zero, for every multi-index $\alpha$. To justify the derivative bound, write $k=t\theta$ with $|\theta|=1$ and factor</p>
<div class="math-display">$$
q(t\theta)=\frac{t^2}{2d}
\left[1-\frac{t^2}{12}\sum_i\theta_i^4+t^4u(t,\theta)\right].
$$</div>
<p>The function $u$ is smooth with bounded derivatives for small $t\ge0$ and all $\theta$, and the bracket is bounded away from zero. After the first two inverse terms are subtracted, $R(t\theta)=t^2v(t,\theta)$ with the same smoothness. Each Cartesian derivative costs at most one power of $t$, giving the assertion.</p>
<p>Apply C5GY with $\beta=2$ to $\chi R$, choosing an integer $N&gt;d+2$. The complementary symbol $(1-\chi)/q$ is smooth and periodic on the torus; repeated integration by parts, with cancelling boundary terms at integer $x$, makes its coefficients decrease faster than every inverse power. It follows that</p>
<div class="math-display">$$
G(x)=2d\,\mathcal F^{-1}\!\left(\frac{\chi}{|k|^2}\right)(x)
+\frac d6\,\mathcal F^{-1}\!\left(\chi\frac{\sum_i k_i^4}{|k|^4}\right)(x)
+O_d(r^{-d-2}).
$$</div>
<p>It remains to evaluate the two homogeneous inverses. With $p_t(x)=(4\pi t)^{-d/2}e^{-r^2/(4t)}$, the Gaussian transform and $|k|^{-2}=\int_0^\infty e^{-t|k|^2}\,dt$ give, for $x\ne0$,</p>
<div class="math-display">$$
\mathcal F^{-1}(|k|^{-2})(x)
=\int_0^\infty p_t(x)\,dt
=\frac{\Gamma(d/2-1)}{4\pi^{d/2}}r^{2-d}.
$$</div>
<p>For the second symbol, use the absolutely convergent identity against Schwartz test functions</p>
<div class="math-display">$$
\frac{\sum_i k_i^4}{|k|^4}
=\int_0^\infty t\sum_i k_i^4e^{-t|k|^2}\,dt.
$$</div>
<p>Indeed its integrand is nonnegative and the time integral is bounded by one, so absolute Fubini applies after multiplication by any integrable test function. Taking inverse transforms, its value off the origin is $\int_0^\infty t\sum_i\partial_i^4p_t(x)\,dt$. This time integral converges locally uniformly away from zero: it has Gaussian decay at small $t$ and order $t^{-d/2-1}$ at large $t$. Direct differentiation yields</p>
<div class="math-display">$$
t\sum_i\partial_i^4p_t(x)
=\left[\frac{\sum_i x_i^4}{16t^3}
       -\frac{3r^2}{4t^2}+\frac{3d}{4t}\right]p_t(x).
$$</div>
<p>Substitute $u=r^2/(4t)$ in each term and use $\Gamma(z+1)=z\Gamma(z)$. The result is</p>
<div class="math-display">$$
\mathcal F^{-1}\!\left(\frac{\sum_i k_i^4}{|k|^4}\right)(x)
=\frac{d(d+2)\Gamma(d/2)}{4\pi^{d/2}}\,r^{-d}Y_4(x/r)
\qquad(x\ne0).
$$</div>
<p>The calculation applies in dimensions three and four as well; it never integrates a divergent biharmonic potential before differentiating. Possible distributional terms supported at the origin do not affect the displayed off-origin formula. C5GY's cutoff assertion now replaces the two cutoff inverses by these formulas with an arbitrarily rapidly decreasing error. Multiplying by $2d$ and $d/6$, respectively, gives the stated constants. Finally, $\Delta\sum_i x_i^4=12|x|^2$ and $\Delta|x|^4=4(d+2)|x|^2$, proving harmonicity. $\square$</p>
<p>In dimension six this becomes</p>
<div class="math-display">$$
G(x)=\frac3{\pi^3}\left[
r^{-4}+\left(8\sum_i(x_i/r)^4-3\right)r^{-6}
\right]+O(r^{-8}).
$$</div>
<p>The coefficient in parentheses is $5$ on a coordinate axis and $-5/3$ on a body diagonal. A radial constant cannot replace it uniformly at order $r^{-6}$. The expansion concerns the walk Green function itself; transferring such a correction to percolation requires the effective-kernel and convolution estimates for that model.</p>


## Dependence on the step law {#section-general-step-correction-link}

<p>The <a href="/articles/branching-random-walk/#section-finite-range-correction">finite-range expansion</a> expresses the corresponding correction for any irreducible symmetric finite-range law through its covariance and normalized fourth moments. For the <a href="/articles/branching-random-walk/#section-box-green-correction">uniform box law $D_L$</a> used above, the angular correction has the opposite sign to the nearest-neighbour one. The formula retains the holding mass at zero and gives the exact normalization change when that atom is removed.</p>



## A positive mass {#section-massive-green-link}

<p>The <a href="/articles/embedded-branching-trees/#section-massive-crossover">near-critical Green profile</a> applies the localized Fourier estimate above with a mass parameter. It gives an absolute $O(|x|^{-d})$ error uniform up to criticality, and a relative error of order $|x|^{-2}$ at bounded mass times distance. The <a href="/articles/embedded-branching-trees/#section-axis-prefactor">exact axis prefactor</a> describes the separate fixed-subcritical limit, where the lattice and continuum exponential rates differ.</p>



## The singularity as killing vanishes {#section-killed-diagram-asymptotics}

<p>For a symmetric probability mass function $p$ of finite support generating $\mathbb Z^d$, write</p>
<div class="math-display">$$
\Sigma=\sum_xp(x)xx^{\mathsf T},\qquad q(k)=1-\widehat p(k),\qquad
C_{\lambda,p}=\sum_{n\ge0}\lambda^np^{*n},\qquad
\mathcal D_s(\lambda)=C_{\lambda,p}^{*s}(0).
$$</div>
<p>Here $s\ge1$ is an integer and $0\le\lambda\le1$; at one, the spatial sums are nonnegative extended sums. The bubble is $\mathcal D_2$, and the triangle is $\mathcal D_3$. They include all zero-step contributions.</p>

<a id="tag-WXT8" data-assertion="theorem" data-title="Finite-range walk diagrams have explicit power singularities and a finite part at the marginal dimension"></a>
<p>Put $\varepsilon=1-\lambda$ and</p>
<div class="math-display">$$
c_p=\frac1{(2\pi)^{d/2}\sqrt{\det\Sigma}}.
$$</div>
<p>As $\lambda\uparrow1$, the following hold for each fixed law $p$:</p>
<div class="math-display">$$
\begin{aligned}
d&lt;2s:&\qquad
\mathcal D_s(\lambda)\sim
c_p\frac{\Gamma(s-d/2)}{\Gamma(s)}\,
\varepsilon^{d/2-s},\\
d=2s:&\qquad
\mathcal D_s(\lambda)=\kappa_{p,s}\log\frac1\varepsilon
+\beta_{p,s}+O_{p,s}\!\left(\varepsilon\log\frac1\varepsilon\right),
\qquad \kappa_{p,s}=\frac{c_p}{\Gamma(s)},\\
d&gt;2s:&\qquad
\mathcal D_s(\lambda)\longrightarrow\mathcal D_s(1)&lt;\infty.
\end{aligned}
$$</div>
<p>The finite constant $\beta_{p,s}$ at $d=2s$ has an explicit convergent integral. Set $q_0(k)=k^{\mathsf T}\Sigma k/2$, and choose $\rho&gt;0$ small enough that $E_\rho=\{k:q_0(k)&lt;\rho^2\}$ lies inside $(-\pi,\pi)^d$. With $H_{s-1}=\sum_{j=1}^{s-1}j^{-1}$ and $H_0=0$,</p>
<div class="math-display">$$
\beta_{p,s}=
\int_{[-\pi,\pi]^d}\left[
q(k)^{-s}-\mathbf1_{E_\rho}(k)q_0(k)^{-s}
\right]\frac{dk}{(2\pi)^d}
+\kappa_{p,s}\bigl(\log\rho^2-H_{s-1}\bigr).
$$</div>
<p>The bracket is integrated as a single function; its separate terms have divergent integrals. The formula is independent of the permitted choice of $\rho$. Neither aperiodicity nor a holding step is required.</p>
<p><em>Proof.</em> The generating assumption makes $\Sigma$ positive definite and makes zero the only zero of $q$ on the frequency torus, as in <a href="/tag/SPSG/">SPSG</a>. Symmetry and finite support give $q=q_0+O(|k|^4)$ near zero. For $0&lt;\lambda&lt;1$, absolute summability and Fourier inversion yield</p>
<div class="math-display">$$
\mathcal D_s(\lambda)=\lambda^{-s}J_s(t),\qquad
J_s(t)=\int(t+q(k))^{-s}\,\frac{dk}{(2\pi)^d},\qquad
t=\frac{1-\lambda}{\lambda}.
$$</div>
<p>The critical identity is obtained by letting $\lambda\uparrow1$. On the spatial side use monotone convergence of the walk coefficients. On $\widehat p\ge0$ the Fourier integrand increases; on $\widehat p&lt;0$ it is bounded by one, so dominated convergence applies there. Thus $\mathcal D_s(1)=\int q^{-s}$, finite exactly when $d&gt;2s$. Points with $\widehat p=-1$ cause no singularity.</p>
<p>If $d&lt;2s$, restrict first to a small neighbourhood of zero and set $k=\sqrt{2t}\,\Sigma^{-1/2}u$. After division by $t^{d/2-s}$ the integrands converge to $(1+|u|^2)^{-s}$, with an integrable bound $C(1+c|u|^2)^{-s}$. The complement contributes $O(1)$ before division and hence vanishes. The Gaussian integral gives</p>
<div class="math-display">$$
\int_{\mathbb R^d}(1+|u|^2)^{-s}\,du
=\frac1{\Gamma(s)}\int_0^\infty v^{s-1}e^{-v}
\left(\frac\pi v\right)^{d/2}dv
=\pi^{d/2}\frac{\Gamma(s-d/2)}{\Gamma(s)}.
$$</div>
<p>The Jacobian is $(2t)^{d/2}/\sqrt{\det\Sigma}$. Since $t\sim\varepsilon$ and $\lambda^{-s}\to1$, this proves the first equivalent.</p>
<p>Now suppose $d=2s$. Subtract the quadratic integral on $E_\rho$ and put</p>
<div class="math-display">$$
R_s(t)=\int\left[(t+q)^{-s}
-\mathbf1_{E_\rho}(t+q_0)^{-s}\right]\frac{dk}{(2\pi)^d}.
$$</div>
<p>Near zero the difference is bounded, uniformly for $t\ge0$, by $C|k|^{2-2s}$, which is integrable in dimension $2s$. Away from zero the denominators stay bounded below. Consequently $R_s(t)\to R_s(0)$.</p>
<p>We also need the rate. For $t&gt;0$ differentiate under the integral. Inside $E_\rho$, the mean value theorem applied to the two denominators bounds the differentiated difference by</p>
<div class="math-display">$$
C\frac{|k|^4}{(t+c|k|^2)^{s+2}}.
$$</div>
<p>Its radial integral is bounded by $C[1+\log(1/t)]$ for small $t$: below $|k|=\sqrt t$ it is bounded, and above that radius its radial integrand is $O(|k|^{-1})$. The complement contributes a bounded derivative. Integrating this estimate from zero to $t$ gives</p>
<div class="math-display">$$R_s(t)=R_s(0)+O_{p,s}\!\left(t\log\frac1t\right).$$</div>
<p>For the quadratic part use $y=\Sigma^{1/2}k/\sqrt2$ and then $v=|y|^2$. The angular integral gives precisely $\kappa_{p,s}$, so</p>
<div class="math-display">$$
\int_{E_\rho}(t+q_0)^{-s}\,\frac{dk}{(2\pi)^d}
=\kappa_{p,s}\int_0^{\rho^2}\frac{v^{s-1}}{(t+v)^s}\,dv
=\kappa_{p,s}\left[
\log\frac{t+\rho^2}{t}
-\sum_{j=1}^{s-1}\frac1j\left(\frac{\rho^2}{t+\rho^2}\right)^j
\right].
$$</div>
<p>The last identity follows by substituting $u=v/(t+v)$ and integrating $u^{s-1}/(1-u)$. The bracket is $\log(1/t)+\log\rho^2-H_{s-1}+O(t)$. Adding $R_s(t)$ proves the finite-part formula for $J_s$. Finally, $\lambda^{-s}=1+O(\varepsilon)$ and $\log(1/t)=\log(1/\varepsilon)+\log\lambda$ give the claimed expansion for $\mathcal D_s$. Its uniquely determined constant also proves independence of $\rho$. $\square$</p>
<p>Holding changes the finite part as well as the logarithmic coefficient. At $d=2s$, if $p_a=(1-a)\delta_0+ap$, $0&lt;a\le1$, then</p>
<div class="math-display">$$
\kappa_{p_a,s}=a^{-s}\kappa_{p,s},\qquad
\beta_{p_a,s}=a^{-s}\bigl(\beta_{p,s}+\kappa_{p,s}\log a\bigr).
$$</div>
<p>Indeed $q_a=aq$ gives $J_{s,a}(t)=a^{-s}J_s(t/a)$. The displayed finite-part transformation follows by substitution, and agrees with $\Sigma_a=a\Sigma$.</p>

## The marginal bubble and triangle coefficients {#section-marginal-killing-coefficients}

<a id="tag-KC8U" data-assertion="corollary" data-title="The six-dimensional triangle logarithm determines the critical approach of the finite bubble"></a>
<p>For ordinary nearest-neighbour walk, let $B_\lambda=C_\lambda^{*2}(0)$, $T_\lambda=C_\lambda^{*3}(0)$ and $\varepsilon=1-\lambda$. As $\lambda\uparrow1$, in dimension four,</p>
<div class="math-display">$$
B_\lambda=\frac4{\pi^2}\log\frac1\varepsilon+\beta_4
+O\!\left(\varepsilon\log\frac1\varepsilon\right),
\qquad \beta_4=\beta_{D,2}.
$$</div>
<p>In dimension six, put $\kappa_6=27/(2\pi^3)$ and $\beta_6=\beta_{D,3}$. Then $B_1&lt;\infty$,</p>
<div class="math-display">$$
T_\lambda=\kappa_6\log\frac1\varepsilon+\beta_6
+O\!\left(\varepsilon\log\frac1\varepsilon\right),
$$</div>
<p>and the bubble has the more precise expansion</p>
<div class="math-display">$$
B_1-B_\lambda
=2\kappa_6\varepsilon\log\frac1\varepsilon
+2(\kappa_6+\beta_6-B_1)\varepsilon
+O\!\left(\varepsilon^2\log\frac1\varepsilon\right).
$$</div>
<p>In particular, $B_1-B_\lambda\sim(27/\pi^3)\varepsilon\log(1/\varepsilon)$.</p>
<p><em>Proof.</em> The covariance is $\Sigma=I/d$, so WXT8 gives</p>
<div class="math-display">$$
\kappa_{D,s}=\frac{d^{d/2}}{(2\pi)^{d/2}\Gamma(s)}
\quad(d=2s).
$$</div>
<p>Substituting $(d,s)=(4,2)$ and $(6,3)$ gives the two logarithmic coefficients. In dimension six the bubble is finite because $6&gt;4$.</p>
<p>For $0&lt;\lambda&lt;1$, differentiation under the bounded Fourier integral gives the exact identity</p>
<div class="math-display">$$
\frac{dB_\lambda}{d\lambda}
=2\int\frac{\widehat D(k)}{(1-\lambda\widehat D(k))^3}\,\frac{dk}{(2\pi)^6}
=\frac2\lambda(T_\lambda-B_\lambda).
$$</div>
<p>Since $B_\lambda\le B_1$ and $T_\lambda=\kappa_6\log(1/\varepsilon)+O(1)$, this identity first gives $B_1-B_\lambda=O(\varepsilon\log(1/\varepsilon))$ by integration. Insert that bound and the full triangle expansion back into the identity to obtain, for $v\downarrow0$,</p>
<div class="math-display">$$
\frac2{1-v}(T_{1-v}-B_{1-v})
=2\kappa_6\log\frac1v+2(\beta_6-B_1)
+O\!\left(v\log\frac1v\right).
$$</div>
<p>Integrating from $v=0$ to $v=\varepsilon$ proves the bubble expansion, because $\int_0^\varepsilon\log(1/v)\,dv=\varepsilon\log(1/\varepsilon)+\varepsilon$. All endpoint integrals converge. $\square$</p>
<p>These coefficients use the killing gap $1-\lambda$. For the continuum mass $m=\sqrt{2d(1-\lambda)/\lambda}$ in <a href="/tag/LEJR/">LEJR</a>, one has $\log(1/\varepsilon)=2\log(1/m)+\log(2d/\lambda)$. Thus the coefficient of $\log(1/m)$ is $8/\pi^2$ for the four-dimensional bubble and $27/\pi^3$ for the six-dimensional triangle. The finite six-dimensional bubble and divergent triangle are compatible; the logarithmic derivative of the bubble records the divergence. These are walk calculations. A percolation analogue requires its own control of the two-point function and its parameter dependence.</p>



## A frequency shift at the marginal dimension {#section-shifted-marginal-profile}

<p>Retain the symmetric finite-range law $p$, covariance $\Sigma$ and symbol $q=1-\widehat p$ of WXT8. Let $s\in\{2,3\}$ and $d=2s$. For $0&lt;\lambda&lt;1$ and a torus vector $h$, define</p>
<div class="math-display">$$
c_\lambda(k)=\frac1{1-\lambda\widehat p(k)},\qquad
\mathcal H_\lambda(h)=\int c_\lambda(k)^{s-1}c_\lambda(k+h)\,\frac{dk}{(2\pi)^d}.
$$</div>
<p>Thus $s=2$ is the shifted bubble and $s=3$ the triangle with one shifted factor. Write $\kappa=\kappa_{p,s}$ and $\beta=\beta_{p,s}$ for the constants in WXT8.</p>

<a id="tag-7PM4" data-assertion="theorem" data-title="The marginal shifted bubble and one-shift triangle share a universal near-critical profile"></a>
<p>Put $\varepsilon=1-\lambda$, $t=\varepsilon/\lambda$ and</p>
<div class="math-display">$$
h=\sqrt{2t}\,\Sigma^{-1/2}v,\qquad
F(r)=\int_0^1\log\bigl(1+u(1-u)r^2\bigr)\,du\quad(r\ge0).
$$</div>
<p>As $\lambda\uparrow1$, uniformly for $v$ in each bounded subset of $\mathbb R^d$,</p>
<div class="math-display">$$
\mathcal H_\lambda(0)-\mathcal H_\lambda(h)\longrightarrow\kappa F(|v|),
\qquad
\mathcal H_\lambda(h)=\kappa\log\frac1\varepsilon+\beta-\kappa F(|v|)+o(1).
$$</div>
<p>The profile satisfies $F(0)=0$ and, for $r&gt;0$,</p>
<div class="math-display">$$
F(r)=\frac{2\sqrt{4+r^2}}r\operatorname{arsinh}(r/2)-2.
$$</div>
<p>Consequently $F(r)=r^2/6-r^4/60+O(r^6)$ as $r\downarrow0$, and $F(r)=2\log r-2+O(r^{-2}\log r)$ as $r\to\infty$. The convergence of the lattice diagrams above is asserted only for bounded $v$.</p>
<p><em>Proof.</em> Set $f_t=(t+q)^{-1}$ and $f_{t,h}(k)=f_t(k+h)$. Translation invariance of the torus integral gives, for $s=2$,</p>
<div class="math-display">$$
\int f_t^2-\int f_tf_{t,h}=\frac12\int(f_t-f_{t,h})^2.
$$</div>
<p>For $s=3$, evenness of $f_t$ also gives $\int f_t^2f_{t,h}=\int f_tf_{t,h}^2$, and hence</p>
<div class="math-display">$$
\int f_t^3-\int f_t^2f_{t,h}
=\frac12\int(f_t+f_{t,h})(f_t-f_{t,h})^2.
$$</div>
<p>These identities express the difference as a nonnegative integral. All integrals here have normalized torus measure. The desired difference is $\lambda^{-s}$ times the appropriate right side.</p>
<p>Choose a smooth cutoff supported near zero and equal to one on a smaller neighbourhood. On its complement, both denominators stay bounded below for small $h$; the difference of the two smooth functions is $O(|h|)$. This part of either squared integral is therefore $O(|h|^2)=O(t)$, uniformly for bounded $v$.</p>
<p>On the cutoff's support put $k=\sqrt{2t}\Sigma^{-1/2}y$ and</p>
<div class="math-display">$$
a_t(y)=\frac{t}{t+q(\sqrt{2t}\Sigma^{-1/2}y)},\qquad
g(y)=\frac1{1+|y|^2}.
$$</div>
<p>The expansion $q(k)=k^{\mathsf T}\Sigma k/2+O(|k|^4)$ shows that $a_t\to g$ uniformly on compact sets, and the shifted factor becomes $a_t(y+v)$. On the scaled neighbourhood, $a_t(y)\le C(1+|y|^2)^{-1}$ and $|\nabla a_t(y)|\le C|y|(1+|y|^2)^{-2}$. For $|v|\le M$ and $|y|&gt;2M+1$, the mean value theorem therefore bounds the scaled squared integrand by</p>
<div class="math-display">$$
C_M(1+|y|)^{-2s-2}.
$$</div>
<p>The same integrand is uniformly bounded on the remaining bounded set. This gives an integrable majorant in dimension $2s$, and uniform convergence of the integrals for bounded $v$. The Jacobian cancels the power $t^{-s}$ from the integrand. The limit is</p>
<div class="math-display">$$
\frac{2^s}{(2\pi)^{2s}\sqrt{\det\Sigma}}
\int_{\mathbb R^{2s}}
\left[g(y)^s-g(y)^{s-1}g(y+v)\right]dy.
$$</div>
<p>The displayed difference is absolutely integrable: at infinity it is $O_M(|y|^{-2s-1})$. The squared identities hold for this continuum integral as well, by first integrating over large balls; their translation boundary terms tend to zero.</p>
<p>To evaluate it, use, for $A,B&gt;0$,</p>
<div class="math-display">$$
\frac1{A^{s-1}B}=(s-1)\int_0^1
\frac{u^{s-2}}{[uA+(1-u)B]^s}\,du.
$$</div>
<p>This follows from the Laplace representations of the two powers by writing their time variables as $ru$ and $r(1-u)$. Completing the square gives</p>
<div class="math-display">$$
u(1+|y|^2)+(1-u)(1+|y+v|^2)
=1+u(1-u)|v|^2+|y+(1-u)v|^2.
$$</div>
<p>Translating the centre in a large-ball integral changes it by $O_M(R^{-1})$ at radius $R$, uniformly in $u$. For $b\ge1$, radial integration, or differentiation in $b$, gives</p>
<div class="math-display">$$
\int_{\mathbb R^{2s}}\left[(1+|y|^2)^{-s}-(b+|y|^2)^{-s}\right]dy
=\frac{\pi^s}{\Gamma(s)}\log b.
$$</div>
<p>Indeed the derivative of the left side is $s\int(b+|y|^2)^{-s-1}dy=\pi^s/[\Gamma(s)b]$, and the value at $b=1$ is zero. It follows that the limit is</p>
<div class="math-display">$$
\kappa(s-1)\int_0^1u^{s-2}
\log\bigl(1+u(1-u)|v|^2\bigr)\,du.
$$</div>
<p>For $s=2$ the weight is one. For $s=3$ it is $2u$, which has the same integral against a function symmetric under $u\mapsto1-u$. Both give $\kappa F(|v|)$. The unshifted expansion in WXT8 supplies the second assertion.</p>
<p>Finally, substituting $2u-1$ and integrating by parts evaluates $F$ as stated. Expansion of its defining logarithm uses $\int_0^1u(1-u)du=1/6$ and $\int_0^1u^2(1-u)^2du=1/30$, giving the small-$r$ formula. The large-$r$ formula follows from the explicit expression. $\square$</p>

## The critical limit at nonzero frequency {#section-critical-shifted-finite-part}

<a id="tag-2RVB" data-assertion="theorem" data-title="Critical marginal shifted diagrams have the same finite part as killing regularization plus twice the logarithmic coefficient"></a>
<p>Under the same hypotheses, for every nonzero torus vector $h$ the integral</p>
<div class="math-display">$$
\mathcal H_1(h)=\int q(k)^{1-s}q(k+h)^{-1}\,\frac{dk}{(2\pi)^d}
$$</div>
<p>is finite and equals $\lim_{\lambda\uparrow1}\mathcal H_\lambda(h)$. As $h\to0$ through nonzero representatives, uniformly in direction,</p>
<div class="math-display">$$
\mathcal H_1(h)=\kappa\log\frac1{q_0(h)}+\beta+2\kappa+o(1),
\qquad q_0(h)=\frac12h^{\mathsf T}\Sigma h.
$$</div>
<p>This is a separate critical-limit assertion; it does not follow by substituting unbounded $v$ into 7PM4.</p>
<p><em>Proof.</em> When $h\ne0$ on the torus, the singularities at zero and $-h$ are distinct. Their orders are $2s-2$ and $2$, both strictly less than $d=2s$. This proves finiteness. For $\lambda\ge1/2$, $c_\lambda\le2/q$, so dominated convergence proves the asserted Abel limit.</p>
<p>Choose the covariance ellipsoid $E_\rho$ from WXT8, small enough that its closure and a fixed neighbourhood lie inside the frequency cube. Subtract the quadratic shifted integral on this ellipsoid. For $k,k+h$ near zero and away from the two singular points, the difference between the lattice and quadratic integrands is bounded by</p>
<div class="math-display">$$
C\left(|k|^{2-2s}+|k+h|^{2-2s}\right).
$$</div>
<p>For $s=2$, this follows by replacing the two inverse factors one at a time and using $q-q_0=O(|k|^4)$. For $s=3$, the first replacement is bounded by $C|k|^{-2}|k+h|^{-2}$ and the second by $C|k|^{-4}$; use $2/(a^2b^2)\le a^{-4}+b^{-4}$. These bounds have integral $O(\delta^2)$ on $|k|\le\delta$, uniformly when $|h|\le\delta$. Off that ball the integrands converge uniformly as $h\to0$. Outside $E_\rho$ the denominators are bounded below. Therefore</p>
<div class="math-display">$$
\mathcal H_1(h)
-\int_{E_\rho}q_0(k)^{1-s}q_0(k+h)^{-1}\,\frac{dk}{(2\pi)^d}
\longrightarrow R_s(0),
$$</div>
<p>where $R_s(0)=\beta-\kappa(\log\rho^2-H_{s-1})$ is precisely the subtracted integral in WXT8. The small-ball estimate makes this convergence uniform in direction.</p>
<p>For the quadratic integral put $y=\Sigma^{1/2}k/\sqrt2$ and $z=\Sigma^{1/2}h/\sqrt2$, so $|z|^2=q_0(h)$. Apply the parameter identity from 7PM4. The denominator becomes</p>
<div class="math-display">$$
|y+(1-u)z|^2+u(1-u)|z|^2.
$$</div>
<p>Replacing the shifted ball of radius $\rho$ by the centred ball changes its integral by $O(|z|)$, uniformly in $u$: the symmetric difference lies near the boundary, where the integrand is uniformly bounded. The radial formula in WXT8, with $b=u(1-u)|z|^2$, gives the remaining integral as</p>
<div class="math-display">$$
\kappa(s-1)\int_0^1u^{s-2}
\left[\log\frac1{|z|^2}+\log\rho^2-H_{s-1}
-\log(u(1-u))+O(|z|^2)\right]du.
$$</div>
<p>The error is uniform for $0&lt;u&lt;1$, and the endpoint logarithms are integrable. For both $s=2$ and $s=3$,</p>
<div class="math-display">$$
-(s-1)\int_0^1u^{s-2}\log(u(1-u))\,du=2.
$$</div>
<p>For $s=2$ this is $-\int\log u-\int\log(1-u)=2$; symmetry gives the same value with the weight $2u$. Add $R_s(0)$ and use $|z|^2=q_0(h)$ to obtain the result. $\square$</p>
<p>For nearest-neighbour walk $q_0(h)=|h|^2/(2d)$. Thus the four-dimensional critical shifted bubble is</p>
<div class="math-display">$$
\mathcal H_1(h)=\frac8{\pi^2}\log\frac1{|h|}
+\beta_4+\frac4{\pi^2}(\log8+2)+o(1),
$$</div>
<p>and the six-dimensional critical one-shift triangle is</p>
<div class="math-display">$$
\mathcal H_1(h)=\frac{27}{\pi^3}\log\frac1{|h|}
+\beta_6+\frac{27}{2\pi^3}(\log12+2)+o(1).
$$</div>
<p>The critical objects here are Fourier integrals and Abel limits; no ordinary convergence of an undamped spatial Fourier series is assumed. These are walk diagrams, and a percolation version would require additional estimates for its own two-point function.</p>



## A logarithmic step-law correction {#section-long-range-killing-link}

<p>For the marginal power-law walk, the symbol is proportional to $|k|^2\log(1/|k|)$ rather than a quadratic form. The <a href="/articles/branching-random-walk/#section-logarithmic-killing">logarithmic boundary calculation</a> determines its divergent coefficients or finite-diagram deficits. The <a href="/articles/branching-random-walk/#section-marginal-killing-expansion">clipped-law specialization</a> gives the leading constants and next logarithmic terms in dimensions two, four and six. It requires no transfer of a walk expansion to percolation.</p>



## Killing and spatial separation {#section-marginal-spatial-link}

<p>The <a href="/articles/branching-random-walk/#section-marginal-spatial-crossover">marginal spatial profile</a> describes a killing time comparable to the time needed to reach a large separation. At the critical diagram dimension, this retains a vanishing fraction of the undamped potential. The <a href="/articles/branching-random-walk/#section-marginal-surviving-fraction">uniform surviving-fraction formula</a> identifies the longer time scale on which a positive fraction remains, including the bubble in dimension four and the triangle in dimension six.</p>
