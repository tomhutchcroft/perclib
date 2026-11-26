---
{
  "id": "completed-fourier-bootstrap",
  "title": "Closing the nearest-neighbour Fourier bootstrap",
  "subtitle": "From small lace coefficients to the critical infrared bound",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "Small coefficient norms improve all three bootstrap functions. Continuity removes the weak-bound premise, and a controlled critical limit gives the triangle estimate and an integrable Fourier density.",
  "context": [
    "Nearest-neighbour bond percolation on $\\mathbb Z^d$, with $d$ sufficiently large.",
    "Fourier integrals use normalized Haar measure on the torus.",
    "All subcritical Fourier series are absolutely convergent by finite susceptibility."
  ],
  "related": [
    "bootstrap-diagram-bounds",
    "fourier-bootstrap",
    "lace-expansion",
    "signed-kernel-moments"
  ],
  "sourceIds": [
    "heydenreich-hofstad"
  ],
  "aliases": [
    "Closing the nearest-neighbour Fourier bootstrap"
  ],
  "prototypeUses": []
}
---

## Improving the mass and Fourier ratio {#section-first}

<p>Keep $j=2dp$, $g=1-\widehat D$, $\lambda=1-1/\chi(p)$, $C=(1-\lambda\widehat D)^{-1}$ and $U=200gV$ from <a href="/tag/NL05/">NL05</a>. Suppose $p<p_c$, $f(p)\le4$, and $d$ is large enough for <a href="/tag/6G0E/">6G0E</a>. Write $\Pi=\Pi_p$ and choose $\varepsilon=c_4/d\le1/2$ so that</p>
<div class="math-display">$$\|\Pi\|_1\le\varepsilon,\qquad M_\Pi(k):=\sum_xh_k(x)|\Pi(x)|\le\varepsilon g(k).$$</div>
<a id="tag-W2WX" data-assertion="proposition" data-title="Small lace coefficients improve the first two bootstrap quantities"></a>
<p>Under these assumptions,</p>
<div class="math-display">$$j\le1+2\varepsilon,\qquad f_2(p)\le1+84\varepsilon.$$</div>
<p>Moreover, with $b=\delta_0+\Pi$, $a=jD*b$ and $A(q)=(1-\widehat a(q))^{-1}$,</p>
<div class="math-display">$$0<A(q)\le tC(q),\qquad t=\frac{1+84\varepsilon}{1-\varepsilon}.$$</div>
<p><em>Proof.</em> Put $m=\widehat\Pi(0)$. Evaluating the lace equation at zero gives</p>
<div class="math-display">$$\lambda=j+\frac m{1+m},\qquad j=\lambda-\frac m{1+m}\le1+2\varepsilon.$$</div>
<p>The minus sign in the second identity is essential; the resulting upper bound is unchanged. Set</p>
<div class="math-display">$$N(q)=\frac{1+\widehat\Pi(q)}{1+m},\qquad
F(q)=\frac{1-j\widehat D(q)[1+\widehat\Pi(q)]}{1+m}.$$</div>
<p>Then $\widehat\tau=N/F$ and</p>
<div class="math-display">$$C(q)^{-1}-F(q)=\frac{g(q)m+j\widehat D(q)[\widehat\Pi(q)-m]}{1+m}.$$</div>
<p>Evenness gives $|\widehat\Pi(q)-m|\le M_\Pi(q)$. Thus $N\le1+4\varepsilon$ and $|C^{-1}-F|\le10\varepsilon g$, using $j\le4$. The original bootstrap bound and <a href="/tag/TTS1/">TTS1</a> give $\widehat\tau(q)g(q)\le4C(q)g(q)\le8$, also at zero by continuity of the product. Therefore</p>
<div class="math-display">$$\frac{\widehat\tau}{C}=N+\widehat\tau(C^{-1}-F)\le1+84\varepsilon.$$</div>
<p>Finally $\widehat b\ge1-\varepsilon>0$. The Fourier equation $\widehat\tau(1-\widehat a)=\widehat b$ and nonnegativity of $\widehat\tau$ imply $\widehat\tau>0$ and $1-\widehat a>0$ at every frequency. Hence $A=\widehat\tau/\widehat b$ is positive and satisfies the claimed bound. This verifies the sign hypothesis needed in the reciprocal lemma, rather than inferring it from evenness.</p>

## Improving the second difference {#section-second}

<a id="tag-12ZK" data-assertion="proposition" data-title="The reciprocal estimate closes the second-difference bootstrap bound"></a>
<p>Under the preceding assumptions, there is an absolute constant $C_*<\infty$ such that</p>
<div class="math-display">$$f_3(p)\le\frac{16}{200}+C_*\varepsilon.$$</div>
<p><em>Proof.</em> The kernels $a,b,\Pi$ are real and even. Since $|a|\le jD*(\delta_0+|\Pi|)$, the cosine addition formula gives</p>
<div class="math-display">$$\begin{aligned}
M_a(k)&\le j\left[g(k)+\|\Pi\|_1g(k)+\widehat D(k)M_\Pi(k)\right]
\le j(1+2\varepsilon)g(k)\le s g(k),\\
\|a\|_1&\le j(1+\varepsilon)\le v,
\qquad s=(1+2\varepsilon)^2,\quad v=(1+2\varepsilon)(1+\varepsilon).
\end{aligned}$$</div>
<p>The displayed convolution identity uses evenness to cancel the sine term; it remains valid when $\widehat D(k)$ is negative. For any summable kernel $q$, Cauchy–Schwarz gives the elementary increment bound</p>
<div class="math-display">$$|\widehat q(l\pm k)-\widehat q(l)|\le\sum_x|q(x)||e^{\pm ik\cdot x}-1|
\le\sqrt{2\|q\|_1M_q(k)}.$$</div>
<p>In particular, an increment of $\widehat a$ is at most $\sqrt{2vs}\sqrt{g(k)}$, and an increment of $\widehat b$ is at most $\sqrt2\,\varepsilon\sqrt{g(k)}$.</p>
<p>Write $A_0=A(l)$, $A_\pm=A(l\pm k)$ and similarly for $C,\widehat a,\widehat b$. Direct subtraction of $\widehat\tau=\widehat b A$ gives</p>
<div class="math-display">$$\Delta_k\widehat\tau(l)=A_0\Delta_k\widehat b(l)
+\sum_{\sigma=\pm1}A_0A_\sigma(\widehat a_\sigma-\widehat a_0)(\widehat b_\sigma-\widehat b_0)
+\widehat b_0\Delta_k A(l).$$</div>
<p>Indeed $A_\sigma-A_0=A_0A_\sigma(\widehat a_\sigma-\widehat a_0)$, and expanding the right side gives the two shifted products and their central subtraction. This avoids an incorrect first-difference product formula; the <a href="/errata/heydenreich-hofstad/#bootstrap-algebra-identities">local algebra entry</a> gives its corrected form.</p>
<p>The first term is at most $2\varepsilon g(k)tC_0$. Since $C_\pm\ge1/2$, $V\ge C_0$. The two middle terms together are at most $2\varepsilon\sqrt{vs}\,t^2g(k)C_0(C_-+C_+)\le2\varepsilon\sqrt{vs}\,t^2g(k)V$.</p>
<p>For the last term use <a href="/tag/84XD/">84XD</a>. W2WX has established that all three reciprocals are positive. Since $g(l)C_0\le2$,</p>
<div class="math-display">$$|\Delta_k A(l)|\le g(k)\left[st^2C_0(C_-+C_+)+16s^2t^3C_-C_+\right]
\le16s^2t^3g(k)V.$$</div>
<p>Here $s,t\ge1$. Also $|\widehat b_0|\le1+\varepsilon$. Divide the three estimates by $U=200g(k)V$, for $k\ne0$, to obtain the explicit bound</p>
<div class="math-display">$$f_3(p)\le\frac{2\varepsilon t+2\varepsilon\sqrt{vs}\,t^2+16(1+\varepsilon)s^2t^3}{200}.$$</div>
<p>This expression equals $16/200$ at $\varepsilon=0$ and has a bounded derivative on $[0,1/2]$. Its difference from $16/200$ is therefore at most $C_*\varepsilon$. The substantial slack comes from the chosen factor 200 in $U$; no sharper constant is needed to close the bootstrap.</p>

## The completed subcritical estimate {#section-bootstrap}

<a id="tag-MYG7" data-assertion="theorem" data-title="The nearest-neighbour Fourier bootstrap closes in sufficiently large dimension"></a>
<p>There are absolute constants $d_0>6$ and $C_0<\infty$ such that, for every $d\ge d_0$ and $0\le p<p_c$,</p>
<div class="math-display">$$f(p)\le1+C_0/d,\qquad
0\le\widehat\tau_p(k)\le\frac{1+C_0/d}{1-\lambda_p\widehat D(k)},\qquad
T_p\le C_0/d,\quad\Delta_p\le1+C_0/d.$$</div>
<p>The estimates of 6G0E, with a common constant, hold at every such parameter.</p>
<p><em>Proof.</em> Fix $K=4$ in 6G0E. Its constants are uniform in $p,d$. W2WX and 12ZK show, at each individual parameter, that $f(p)\le4$ implies $f(p)\le1+C_0/d$. Choose $d_0$ large enough that the latter quantity is at most three and all preceding estimates apply. By NL05, $f$ is continuous, $f(0)=1$, and it cannot cross the forbidden interval $(3,4]$. Thus $f\le3$ throughout the subcritical interval. Apply the same improvement once more at each parameter to obtain $f\le1+C_0/d$. The triangle estimates follow from 54IO. The coefficient conclusion is 6G0E with $K=4$.</p>
<p>The implication is pointwise in $p$: it does not assume that the weak bound already holds on the whole subcritical interval. This is what makes the continuity argument noncircular.</p>

## Passing to criticality {#section-critical}

<a id="tag-F7N7" data-assertion="theorem" data-title="The completed bootstrap gives the critical lace equation and an integrable Fourier density"></a>
<p>After increasing $d_0,C_0$ if necessary, for $d\ge d_0$ one has</p>
<div class="math-display">$$1\le2dp_c\le1+C_0/d,\qquad \Delta_c\le1+C_0/d,\qquad T_c\le C_0/d,\qquad\theta(p_c)=0.$$</div>
<p>The critical signed kernel has $\|\Pi_c\|_1+\sum_x|x|^2|\Pi_c(x)|\le C_0/d$, and $\Pi_p\to\Pi_c$ in $\ell^1$ as $p\uparrow p_c$. Moreover,</p>
<div class="math-display">$$j_c[1+\widehat\Pi_c(0)]=1,\qquad
Q_c(k)=\frac{1+\widehat\Pi_c(k)}{1-j_c\widehat D(k)[1+\widehat\Pi_c(k)]}\quad(k\ne0)$$</div>
<p>is a nonnegative integrable Fourier density with</p>
<div class="math-display">$$Q_c(k)\le\frac{1+C_0/d}{g(k)},\qquad
\tau_c(x)=\int e^{-ik\cdot x}Q_c(k)\,dk.$$</div>
<p>This density does not assert absolute summability of the critical two-point function.</p>
<p><em>Proof.</em> Every finite connection has a finite path witness, so $\tau_p(x)\uparrow\tau_c(x)$. Monotone convergence of the nonnegative diagrams passes MYG7's bounds on $T,\Delta$ to criticality. Finite $\Delta_c$ implies $\theta(p_c)=0$ by <a href="/tag/5W46/">5W46</a>. For large $d$, $2T_c\Delta_c<1$, so <a href="/tag/3W22/">3W22</a> gives the critical spatial equation, coefficient convergence and critical normalization. Its proof handles the nonmonotone cutting events by dominated convergence of their witness sums. The uniform coefficient bounds in 6G0E pass to each critical coefficient by Fatou; a second application over orders and vertices gives the claimed absolute norm and moment bound.</p>
<p>For $j<1$, the first-step inequality iterated against $\tau\le1$ gives $\chi(p)\le\sum_{n\ge0}j^n<\infty$, hence $2dp_c\ge1$. The upper bound follows by letting $p\uparrow p_c$ in the bound on $j$ in MYG7. Critical susceptibility diverges by <a href="/tag/JQLC/">JQLC</a>; monotone convergence implies $\chi(p)\uparrow\infty$ and $\lambda_p\uparrow1$.</p>
<p>To justify the density, set $b_p=1+\widehat\Pi_p$ and $E_p=1-j\widehat D b_p$. The norm bound gives $b_p\ge1-\varepsilon$ with a fixed $\varepsilon=O(1/d)<1$. W2WX and MYG7 imply</p>
<div class="math-display">$$E_p(k)=\frac{b_p(k)}{\widehat\tau_p(k)}
\ge\frac{1-\varepsilon}{1+C_0/d}[1-\lambda_p\widehat D(k)].$$</div>
<p>Uniform convergence of $\widehat\Pi_p$ gives the corresponding critical denominator bound by a positive constant times $g(k)$. It is therefore nonzero for $k\ne0$, and the subcritical quotients converge there to $Q_c$. The sharper MYG7 bound passes to the limit, giving $Q_c\le(1+C_0/d)/g$.</p>
<p>For the inverse formula, TTS1 bounds all subcritical quotients by $2(1+C_0/d)/g$. This is integrable for $d>2$. Dominated convergence in the subcritical inverse formula, together with the spatial limit $\tau_p(x)\uparrow\tau_c(x)$, proves the stated identity. The value at the single frequency zero is immaterial to the integral.</p>
<p>The <a href="/coverage/sources/heydenreich-hofstad-2017-bootstrap/">Chapter 8 map</a> records the remaining illustrative ODE and finer-asymptotic exercises separately. The argument here is for nearest-neighbour percolation in sufficiently large dimension; it does not establish the spread-out exercise or any reverse-BK statement.</p>

## One explicit dimension threshold {#section-explicit-dimension}

<p>The estimates above give a numerical dimension threshold once the diagram constants are retained. The following deliberately coarse bound is an independent quantification of this proof. It is not a claimed threshold from the source, and makes no assertion about dimensions near six.</p>

<a id="tag-7GNW" data-assertion="theorem" data-title="An explicit dimension bound for the nearest-neighbour infrared estimate and spatial asymptotic"></a>
<p>For nearest-neighbour bond percolation on $\mathbb Z^d$, suppose $d\ge10^{11}$ and put $\varepsilon=50000000/d\le1/2000$. For every $0\le p<p_c$,</p>
<div class="math-display">$$f(p)\le1+84\varepsilon\le\frac{521}{500},\qquad
2dp\le1+2\varepsilon\le\frac{1001}{1000},\qquad
0\le\widehat\tau_p(k)\le\frac{1+84\varepsilon}{1-\lambda_p\widehat D(k)}.$$</div>
<p>At criticality all clusters are finite almost surely, $1\le j_c=2dp_c\le1+2\varepsilon$, and the critical density and lace kernel satisfy</p>
<div class="math-display">$$\begin{aligned}
\tau_c(x)&=\int e^{-ik\cdot x}R(k)\,dk,\qquad
0\le R(k)\le\frac{1+84\varepsilon}{g(k)},\\
R&=\frac{\widehat b}{1-\widehat Q},\qquad
b=\delta_0+\Pi_c,\quad Q=j_cD*b,\quad \sum_xQ(x)=1,\\
1-\widehat Q(k)&\ge\frac{1999}{2084}g(k),\qquad
\sum_{N,x}\Pi_c^{(N)}(x)\le\frac{220}{d},\quad
\sum_{N,x}|x|^2\Pi_c^{(N)}(x)\le\varepsilon.
\end{aligned}$$</div>
<p>The density inequalities are understood off zero. In particular, the sixth-norm quantity of <a href="/tag/FWHO/">FWHO</a> satisfies $\rho_6<407/500$. Hence, with $\langle x\rangle=\max\{1,|x|\}$ and $A_d=d\Gamma(d/2-1)/(2\pi^{d/2})$,</p>
<div class="math-display">$$\tau_c(x)=\frac{A_d}{j_ca_c}\langle x\rangle^{2-d}
+O_d\!\left(\langle x\rangle^{-(d-2+4/(d+2))}\right),\qquad
a_c=1+j_c\sum_x|x|^2\Pi_c(x)>0.$$</div>
<p>The full nonnegative coefficient series also has the uniform pointwise bound $C_d\langle x\rangle^{-2(d-2)}$ for $p\le p_c$. Its weighted summability and critical continuity hold for every $0\le s<d-4$, in the precise form stated in FWHO.</p>
<p><em>Proof.</em> Fix a subcritical parameter at which $f(p)\le2$. <a href="/tag/66SP/">66SP</a> supplies the full lace equation and the two coefficient bounds used in W2WX, both with constant $\varepsilon$, since $220/d\le\varepsilon$. The algebra in W2WX and12ZK uses only those bounds, the equation and $f(p)\le4$; it does not require an additional dimension threshold. Repeating it gives</p>
<div class="math-display">$$j\le1+2\varepsilon,\qquad f_2\le1+84\varepsilon,\qquad
f_3\le\frac{2\varepsilon t+2\varepsilon\sqrt{vs}\,t^2+16(1+\varepsilon)s^2t^3}{200},$$</div>
<p>where $s=(1+2\varepsilon)^2$, $v=(1+2\varepsilon)(1+\varepsilon)$ and $t=(1+84\varepsilon)/(1-\varepsilon)$. Replace $2\sqrt{vs}$ by $v+s$. The resulting rational expression is increasing on $[0,1/2000]$, and substitution at $1/2000$ gives a value below $1/10$. Thus</p>
<div class="math-display">$$f(p)\le2\quad\Longrightarrow\quad
f(p)\le\frac{521}{500}<\frac{21}{20}<2.$$</div>
<p>NL05 applies with the fixed bounds $21/20$ and two. It gives $f\le21/20$ throughout the subcritical interval; applying the same estimates once more at each parameter proves the sharper bounds in the statement. This is a pointwise improvement followed by continuity, not an assumed bound on the entire parameter interval.</p>
<p>NOTF now holds at every subcritical parameter. Monotone convergence of the spatial diagrams gives $T_c\le63/d$, $\Delta_c\le1+189/(2d)$ and $2T_c\Delta_c<1$. Finite $\Delta_c$ gives $\theta(p_c)=0$, and transitivity and countability make every critical cluster finite almost surely. The critical convergence argument 3W22 therefore supplies the full critical equation, $\ell^1$ convergence of the signed kernels and $j_c[1+\widehat\Pi_c(0)]=1$. Its fixed-order convergence, followed by Fatou in the nonnegative sums of 66SP, gives the two critical coefficient bounds. In particular $b,Q$ have finite absolute second moments; their reflection and permutation symmetries follow from those of the model.</p>
<p>As in F7N7, first-step iteration below $j=1$ gives $j_c\ge1$, and divergence of critical susceptibility gives $\lambda_p\uparrow1$. Put $b_p=1+\widehat\Pi_p$ and $E_p=1-j\widehat D b_p$. The numerator satisfies $b_p\ge1-\varepsilon>0$, and the Fourier equation and positivity give</p>
<div class="math-display">$$E_p(k)\ge\frac{1-\varepsilon}{1+84\varepsilon}
[1-\lambda_p\widehat D(k)].$$</div>
<p>Uniform convergence of the coefficient transforms passes this inequality to criticality. Its constant is at least $1999/2084$. The critical denominator is consequently positive off zero, and the quotients converge there to the stated nonnegative density. TTS1 supplies the integrable envelope $2(1+84\varepsilon)/g$, so dominated convergence in Fourier inversion identifies the density with $\tau_c$. This also passes the sharper subcritical upper bound to the limit.</p>
<p>Both the critical infrared amplitude and $j_c$ are at most $21/20$. Since $d\ge40$, <a href="/tag/NI0W/">NI0W</a> gives $\rho_6<407/500$. The gap just proved implies a positive multiple of $|k|^2$ on the torus, because $g(k)\ge2|k|^2/(\pi^2d)$. We have thus supplied every hypothesis of FWHO: finite critical clusters, the inverse Fourier representation, absolute second moments, the symmetries, normalization, quadratic gap and sixth-norm smallness. Its conclusions give the spatial expansion, coefficient tail and weighted continuity above.</p>
<p>The dimension $10^{11}$ comes from generous upper bounds in the weighted diagrams. The previous conditional results at dimensions 15, 40, 64 and100 are unchanged; their hypotheses have not been established at those dimensions. No optimal dimension bound or new source correction is claimed.</p>

<details><summary>Exact numerical certificate</summary>
<p>The standard-library Python calculation below checks the finite walk sum, its analytic remainder, every rounded diagram constant and the final bootstrap inequalities. The written argument supplies the inequalities to which these rational comparisons apply.</p>
<pre id="explicit-bootstrap-certificate-code"><code>#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
&quot;&quot;&quot;Exact arithmetic for NOTF, 66SP and 7GNW; the analytic estimates are in the wiki.&quot;&quot;&quot;
from fractions import Fraction as F
from math import comb
import json

# LKS9: certify I_(40,6) from returns through length 128 and an upper tail.
M = 64
counts = [1] + [0] * M
weights = [[comb(2*m, 2*k) * comb(2*k, k) for k in range(m+1)]
           for m in range(M+1)]
for d in range(1, 41):
    counts = [sum(weights[m][k] * counts[m-k] for k in range(m+1))
              for m in range(M+1)]
    assert F(counts[2], (2*d)**4) == F(3*(2*d-1), 8*d**3)
    if d in (1, 2):
        assert all(counts[m] == comb(2*m, m)**d for m in range(M+1))
partial = sum(F(comb(2*m+5, 5) * counts[m], 80**(2*m))
              for m in range(M+1))
tail = (F(8, 15) * F(22*40, 7*16)**20
        * (1 + F(5, 2*(M+1)))**5 * F(M)**(-14) / 14)
I = F(669, 500)
assert partial + tail &lt; I
assert I &lt; F(6, 5)**2 and I &lt; F(6, 5)**3
assert F(3, 4)*I &lt; F(11, 10)**2

# NOTF: retain the constants in the triangle, pair and H estimates.
assert 1 + 4*(2+4+8)*F(11, 10) &lt; 63
assert 2 + 16*F(11, 10) + 300*16*F(11, 10) &lt; 5300
assert 16*301*F(6, 5) &lt; 5800
assert 300*2**10*F(6, 5)**2*F(11, 10) &lt; 487000

# 66SP: each bound is monotone in 1/d, so check d=14000.
d = 14000
assert F(63, d) &lt;= F(1, 100)
assert 1 + F(189, 2*d) &lt;= F(11, 10)
assert 2*63*F(11, 10) &lt;= 140
r = F(1, 100)
assert (10-9*r+3*r*r)/(1-r)**3 &lt;= 11
assert (5-r)/(1-r)**3 &lt;= 6
assert 63 + F(154)/(1-r) &lt; 220
low = 2*5300 + 16*63*F(11, 10)*5800
total = low + 25520*11*140 + 6*F(121, 100)*(3654+487000)
assert low == 6441640
assert total == F(1232614701, 25) &lt; 50000000

# 7GNW: the rational majorant replaces 2 sqrt(vs) by v+s.
dimension = 10**11
epsilon = F(50000000, dimension)
assert dimension &gt;= 14000 and epsilon == F(1, 2000)
s = (1+2*epsilon)**2
v = (1+2*epsilon)*(1+epsilon)
t = (1+84*epsilon)/(1-epsilon)
f3 = (2*epsilon*t + epsilon*(v+s)*t**2
      + 16*(1+epsilon)*s*s*t**3)/200
assert f3 &lt; F(1, 10)
assert 1+84*epsilon == F(521, 500) &lt; F(21, 20) &lt; 2
assert 1+2*epsilon == F(1001, 1000) &lt; F(21, 20)
assert (1-epsilon)/(1+84*epsilon) == F(1999, 2084)
print(json.dumps({&quot;result&quot;: &quot;passed&quot;, &quot;arithmetic&quot;: &quot;exact rational&quot;,
                  &quot;dimension_at_least&quot;: dimension, &quot;epsilon_at_most&quot;: str(epsilon),
                  &quot;coefficient_weight_constant&quot;: str(total),
                  &quot;infrared_amplitude_at_most&quot;: &quot;521/500&quot;,
                  &quot;j_c_at_most&quot;: &quot;1001/1000&quot;, &quot;f3_upper&quot;: &quot;1/10&quot;,
                  &quot;critical_gap_at_least&quot;: &quot;1999/2084&quot;}, indent=2))
</code></pre>
</details>
