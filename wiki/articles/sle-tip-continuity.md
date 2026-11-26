---
{
  "id": "sle-tip-continuity",
  "title": "Joint continuity at the SLE tip",
  "subtitle": "Derivative tails on a deterministic time grid give uniform radial limits",
  "kind": "method",
  "category": "General theory",
  "summary": "A short-time Loewner comparison converts derivative estimates at deterministic times into bounds throughout a space-time strip. Brownian oscillation and Borel–Cantelli give radial convergence uniformly in time, together with a time modulus for the limiting curve.",
  "context": [
    "Ordinary chordal SLE with kappa greater than zero; no continuous trace is assumed.",
    "The joint-continuity argument applies when kappa is different from eight, including kappa equal to four.",
    "The deterministic Loewner trace-generation criterion is a separate step. Joint continuity of the radial tip map does not here assert continuity at every real boundary point or identify the generated hulls.",
    "At kappa eight, the fixed-time Holder theorem gives radial limits for almost every time, but the uniform argument below has no positive exponent."
  ],
  "related": ["sle-derivative-estimates", "sle-conformal-radius", "sle-space-filling"],
  "sourceIds": ["rohde-schramm-basic-sle-2005"],
  "aliases": ["SLE moving tip", "uniform radial limit", "SLE time Holder continuity"],
  "prototypeUses": []
}
---

## A short-time comparison {#section-short-time}

<p>For a continuous real driving function $U$, let $g_t$ be the chordal Loewner maps, $f_t=g_t^{-1}$, and $\widehat f_t(z)=f_t(z+U_t)$. Write</p>
<div class="math-display">$$F(y,t)=\widehat f_t(iy),\qquad y&gt;0.$$</div>
<p>The map $F$ is jointly continuous away from $y=0$: the backward Loewner equation starts at positive height, stays above that height, and depends continuously on its starting point, time and driving function.</p>

<a id="tag-4ENF" data-assertion="proposition" data-title="Small driving oscillation localizes a short Loewner interval in one inverse map"></a>
<p>Let $h&gt;0$, $0\leq\ell\leq h^2$, and suppose</p>
<div class="math-display">$$\sup_{s\leq u\leq s+\ell}|U_u-U_s|\leq h.$$</div>
<p>There is a universal constant $C$ such that</p>
<div class="math-display">$$\operatorname{diam}\{F(y,t):h/2\leq y\leq h,\ s\leq t\leq s+\ell\}
\leq Ch\,|\widehat f_s'(ih)|.$$</div>
<p><em>Proof.</em> Fix $t,y$ in this rectangle and run the Loewner equation backward from $U_t+iy$ to time $s$. After subtracting $U_s$, the backward solution $Z_v$, $0\leq v\leq t-s$, solves</p>
<div class="math-display">$$\frac{dZ_v}{dv}=-\frac2{Z_v-(U_{t-v}-U_s)},\qquad Z_0=U_t-U_s+iy.$$</div>
<p>Its real part remains in $[-h,h]$: at either endpoint the real vector field points inward, since the driving values lie in this interval. Its imaginary part $Y_v$ increases and satisfies $d(Y_v^2)/dv\leq4$. Hence the endpoint $w=Z_{t-s}$ lies in the rectangle</p>
<div class="math-display">$$Q_h=\{x+iv:|x|\leq h,\ h/2\leq v\leq\sqrt5h\}.$$</div>
<p>The flow composition identity gives $F(y,t)=\widehat f_s(w)$. The rescaled rectangle $Q_h/h$ is a fixed compact subset of $\mathbb H$ containing $i$. Koebe distortion bounds $|\widehat f_s'|$ throughout $Q_h$ by a universal multiple of $|\widehat f_s'(ih)|$. Integrating along straight segments in this convex rectangle proves the diameter bound.</p>

## Uniform convergence in time {#section-uniform-limit}

<a id="tag-N7TT" data-assertion="theorem" data-title="The radial SLE tip map extends jointly continuously for kappa different from eight"></a>
<p>Let $U_t=\sqrt\kappa B_t$ with $\kappa&gt;0$, $\kappa\ne8$, and put</p>
<div class="math-display">$$b=\frac{\kappa+8}{4\kappa},\qquad
a=\frac{(\kappa+8)(3\kappa+8)}{32\kappa},\qquad
\lambda=\frac{(\kappa+8)^2}{16\kappa},\qquad
q=\max\{a,\lambda\},\qquad \sigma_0=\frac{\lambda-2}{q}.$$</div>
<p>Then $0&lt;\sigma_0&lt;1$. Almost surely there is a continuous $\gamma:[0,\infty)\to\overline{\mathbb H}$ with $\gamma(0)=0$ such that, for every $T&lt;\infty$ and $0&lt;\sigma&lt;\sigma_0$, some finite random $C_{T,\sigma}$ satisfies</p>
<div class="math-display">$$\sup_{0\leq t\leq T}|F(y,t)-\gamma(t)|\leq C_{T,\sigma}y^\sigma
\qquad(0&lt;y\leq1).$$</div>
<p>In particular $F$ extends continuously to $[0,\infty)\times[0,\infty)$ by setting $F(0,t)=\gamma(t)$.</p>
<p><em>Proof.</em> First take $T=1$ and fix $0&lt;\sigma&lt;\sigma_0$. The displayed parameters are those of <a href="/tag/M7AF/">M7AF</a>; $b$ lies in its allowed range. Moreover</p>
<div class="math-display">$$\lambda-2=\frac{(\kappa-8)^2}{16\kappa}&gt;0.$$</div>
<p>Let $h_n=2^{-n}$ and $\Delta_n=h_n^2/(n+1)^2$. Partition $[0,1]$ into $m_n=4^n(n+1)^2$ intervals $I_{n,j}=[j\Delta_n,(j+1)\Delta_n]$. Reflection and the Gaussian tail bound give</p>
<div class="math-display">$$\mathbb P\left(\sup_{t\in I_{n,j}}|U_t-U_{j\Delta_n}|&gt;h_n\right)
\leq4\exp\left(-\frac{(n+1)^2}{2\kappa}\right).$$</div>
<p>Multiplication by $m_n$ leaves a summable sequence in $n$. Thus, almost surely, every interval at every sufficiently fine level has driving oscillation at most $h_n$.</p>
<p>At the deterministic left endpoints, M7AF with $x=0$, $y=h_n$ and $\delta=h_n^\sigma$ gives</p>
<div class="math-display">$$\begin{aligned}
\sum_{n\geq0}\sum_{j=0}^{m_n-1}
\mathbb P\left(|\widehat f_{j\Delta_n}'(ih_n)|\geq h_n^{\sigma-1}\right)
&\leq C_\kappa\sum_{n\geq0}(n+1)^2
2^{-n(\lambda-2-\sigma q)}\\
&lt;\infty.
\end{aligned}$$</div>
<p>No independence between these events is needed. Borel–Cantelli and 4ENF imply that, almost surely, for all sufficiently large $n$ and every $j$,</p>
<div class="math-display">$$\operatorname{diam}F([h_n/2,h_n]\times I_{n,j})\leq C h_n^\sigma.$$</div>
<p>The finitely many remaining rectangles have finite diameter by interior continuity. Enlarging a random constant therefore makes this estimate valid for every $n,j$.</p>
<p>For fixed $t$, consecutive dyadic heights belong to one of these rectangles. Summing their differences gives</p>
<div class="math-display">$$\sup_{t\in[0,1]}|F(h_m,t)-F(h_n,t)|
\leq C\sum_{k=n}^{m-1}h_k^\sigma\leq\frac{C h_n^\sigma}{1-2^{-\sigma}}\qquad(m&gt;n).$$</div>
<p>Hence the continuous functions $F(h_n,\cdot)$ converge uniformly to a continuous function $\gamma$. The same rectangle bound for $h_{n+1}\leq y\leq h_n$ extends the estimate from dyadic heights to every $y$, with error at most $C'y^\sigma$. Since $F(y,0)=iy$, the limit starts at zero. Uniform convergence and continuity of $\gamma$ imply joint continuity at $y=0$.</p>
<p>Brownian scaling gives the result on each fixed finite time interval. Intersect the resulting probability-one events over positive integer horizons and over a sequence of exponents increasing to $\sigma_0$. The estimates for these exponents imply those for every smaller positive exponent. The limits agree on overlapping intervals by uniqueness. This gives a single probability-one event with all the asserted quantifiers.</p>
<p>This proves the radial joint-continuity assertion of Rohde–Schramm Theorem 3.6. Its proof partitions time using reversed Brownian stopping times. Here the shorter deterministic intervals cost only the polynomial factor $(n+1)^2$, which the strict exponent inequality absorbs.</p>

## A time modulus for the limiting curve {#section-time-modulus}

<a id="tag-MV6M" data-assertion="corollary" data-title="The radial tip curve has a logarithmic time modulus and positive Holder exponents"></a>
<p>On the probability-one event of N7TT, for every finite $T$ and $0&lt;\sigma&lt;\sigma_0$,</p>
<div class="math-display">$$|\gamma(t)-\gamma(s)|\leq C_{T,\sigma}|t-s|^{\sigma/2}
\bigl(1+|\log|t-s||\bigr)^\sigma
\qquad(0&lt;|t-s|\leq1,\ s,t\in[0,T]).$$</div>
<p>Consequently $\gamma$ is locally $\beta$-Hölder for every $0&lt;\beta&lt;\sigma_0/2$.</p>
<p><em>Proof.</em> Work first on $[0,1]$ with the rectangles in the preceding proof. Put $u=|t-s|$ and choose $n$ so that $\Delta_{n+1}&lt;u\leq\Delta_n$. The points $s,t$ lie in the same or adjacent level-$n$ time intervals. At their common endpoint the two rectangles have a common image point, so</p>
<div class="math-display">$$|F(h_n,t)-F(h_n,s)|\leq2C h_n^\sigma.$$</div>
<p>The uniform radial error gives the same order for $|\gamma(t)-\gamma(s)|$. Since $\Delta_n/\Delta_{n+1}\leq16$, we have $h_n\leq4\sqrt u\,(n+1)$. Also $n\leq\log(1/u)/\log4$. These inequalities prove the displayed modulus. Scaling and an adjustment of the finite random constant handle a general horizon. Given $\beta&lt;\sigma_0/2$, choose $2\beta&lt;\sigma&lt;\sigma_0$ and absorb the logarithmic factor into $u^{\beta-\sigma/2}$.</p>
<p>The available exponent is explicit:</p>
<div class="math-display">$$\frac{\sigma_0}{2}=\begin{cases}
\displaystyle\frac{(\kappa-8)^2}{2(\kappa+8)^2},&amp;0&lt;\kappa&lt;8,\\[4pt]
\displaystyle\frac{(\kappa-8)^2}{(\kappa+8)(3\kappa+8)},&amp;\kappa&gt;8.
\end{cases}$$</div>
<p>These are sufficient exponents from this proof; no optimality claim is made. A continuous radial tip curve has been constructed. Identifying the Loewner domains as the unbounded components of its complement still requires the deterministic trace-generation theorem.</p>

## What remains at kappa eight {#section-eight}

<a id="tag-YVFR" data-assertion="corollary" data-title="At kappa eight the radial tip limit exists for almost every time almost surely"></a>
<p>For $\kappa=8$, almost surely $\lim_{y\downarrow0}\widehat f_t(iy)$ exists as a finite complex number for Lebesgue-almost every $t\geq0$.</p>
<p><em>Proof.</em> At each fixed deterministic time, <a href="/tag/OLNV/">OLNV</a> gives a continuous boundary extension almost surely. The exceptional set of pairs $(\omega,t)$ where the radial limit fails is measurable: the Cauchy criterion can be expressed using countably many rational heights, and continuity at positive height makes that criterion equivalent to the full radial limit. Fubini on each finite time interval gives zero exceptional time measure for almost every sample. Intersect over integer horizons.</p>
<p>This does not give convergence uniformly in time or a continuous version at all times. At $\kappa=8$ the chosen parameter has $\lambda=2$, leaving no positive summability margin in N7TT. The source's later update cites a separate proof of the full kappa-eight trace theorem; that input is not replaced here.</p>


## Identification of the generated hulls {#section-generation-update}

<p>The deterministic step is now proved in <a href="/tag/N2VO/">N2VO</a>. A first-contact argument shows that any arc avoiding the continuous radial curve remains in the Loewner domain. Classical boundary extension then gives unrestricted inverse-map limits. Consequently <a href="/tag/MN2A/">MN2A</a> identifies the curve constructed above as the generating SLE trace for positive kappa different from eight. No extra uniform-convergence hypothesis is needed for the deterministic criterion. The limitation at kappa eight described above remains.</p>
