---
{
  "id": "sle-derivative-estimates",
  "title": "SLE inverse-map derivatives",
  "subtitle": "A height-clock martingale yields moments, tails and Hölder continuity",
  "kind": "method",
  "category": "General theory",
  "summary": "Reverse Loewner flow identifies inverse-map derivatives. In logarithmic height time, a positive martingale has bounded stochastic coefficient, giving exact weighted moments and a direct fixed-time tail bound. A dyadic grid then proves local Hölder continuity up to the real boundary.",
  "context": [
    "These are ordinary chordal SLE estimates for kappa greater than zero. They do not assume that a continuous trace has already been constructed.",
    "The inputs are the Loewner conformal-map theorem, local uniqueness for stochastic differential equations, Brownian time change, Itô calculus, the bounded-coefficient exponential-martingale criterion, Schwarz–Pick and Koebe distortion.",
    "Hölder continuity below is asserted at each fixed deterministic time. Joint continuity at the moving driving point, trace generation and the separate theorem converting conformal-map regularity into zero-area hull boundaries remain distinct steps.",
    "The fixed-time upper bound removes a logarithmic loss from a valid source estimate. A different comparison in the lower-bound proof of Lemma 3.3 needs a bounded-factor repair, recorded provisionally in the errata."
  ],
  "related": ["sle-conformal-radius", "sle-space-filling", "sle-boundary-avoidance"],
  "sourceIds": ["rohde-schramm-basic-sle-2005"],
  "aliases": ["reverse SLE derivative moments", "SLE Hölder continuity", "logarithmic height clock"],
  "prototypeUses": []
}
---

## Reversing the flow at a fixed time {#section-reverse-flow}

<p>Let $g_t$ solve $\partial_tg_t(z)=2/(g_t(z)-U_t)$, where $U_t=\sqrt\kappa B_t$, and put $\widehat f_t(z)=g_t^{-1}(z+U_t)$. A reverse Loewner flow is the solution</p>
<div class="math-display">$$\partial_tH_t(z)=-\frac2{H_t(z)-U_t},\qquad H_0(z)=z.$$</div>
<p>Its imaginary part increases, so it is defined on the whole upper half-plane at every finite time.</p>

<a id="tag-HHBC" data-assertion="proposition" data-title="At each fixed time the reverse Loewner map has the law of the centered inverse SLE map"></a>
<p>For each fixed $T\geq0$, as random conformal maps on $\mathbb H$,</p>
<div class="math-display">$$H_T\ \overset{\mathrm{law}}=\ \widehat f_T-U_T.$$</div>
<p>In particular their derivatives have the same law. This does not assert equality of the processes indexed by $T$.</p>
<p><em>Proof.</em> To invert $g_T$, start at $z+U_T$ and solve backward for time $s\in[0,T]$:</p>
<div class="math-display">$$\partial_s\phi_s=-\frac2{\phi_s-U_{T-s}},\qquad \phi_0=z+U_T.$$</div>
<p>Then $\phi_T=\widehat f_T(z)$. The translated flow $h_s=\phi_s-U_T$ starts at $z$ and has reverse driving function $V_s=U_{T-s}-U_T$. Brownian reversal on this fixed interval makes $(V_s)_{0\leq s\leq T}$ equal in law to $(U_s)_{0\leq s\leq T}$. Uniqueness of the driven flow proves the map identity in law, including its spatial derivatives.</p>

## Height as time {#section-height-clock}

<p>It is useful to treat both directions together. For $\eta\in\{-1,1\}$ let</p>
<div class="math-display">$$\partial_tH_t^{\eta}(z)=-\frac{2\eta}{H_t^{\eta}(z)-U_t},\qquad
Z_t=H_t^{\eta}(z)-U_t=X_t+iY_t,\qquad D_t=|(H_t^{\eta})'(z)|.$$</div>
<p>Thus $\eta=1$ is reverse flow and $\eta=-1$ is forward flow, up to its lifetime. Write $z=x+iy$.</p>

<a id="tag-O0VQ" data-assertion="proposition" data-title="Logarithmic height gives a global ratio diffusion and a two-sided derivative comparison"></a>
<p>The increasing clock $s=\eta\log(Y_t/y)$ runs through every finite nonnegative value. In this clock, $R_s=X_{t(s)}/Y_{t(s)}$ satisfies</p>
<div class="math-display">$$dR_s=-2\eta R_s\,ds+\sqrt{\kappa/2}\sqrt{1+R_s^2}\,dW_s,
\qquad Y_{t(s)}=ye^{\eta s},$$</div>
<div class="math-display">$$\frac{dt}{ds}=\frac{Y_{t(s)}^2(1+R_s^2)}2,
\qquad \frac{d\log D_{t(s)}}{ds}=\eta\frac{R_s^2-1}{R_s^2+1}.$$</div>
<p>Consequently, for any two physical times before the flow ends,</p>
<div class="math-display">$$\left|\log\frac{D_{t_2}}{D_{t_1}}\right|
\leq\left|\log\frac{Y_{t_2}}{Y_{t_1}}\right|.$$</div>
<p><em>Proof.</em> The centered flow obeys $dZ=-2\eta Z^{-1}dt-\sqrt\kappa\,dB$. Its imaginary part gives $ds/dt=2/|Z|^2$. Applying Itô to $X/Y$ and changing time gives the displayed diffusion, after changing the sign of the Brownian motion if necessary. Differentiating the Loewner equation in $z$ gives $\partial_t\log D=2\eta\operatorname{Re}(Z^{-2})$, hence the last derivative formula.</p>
<p>The ratio diffusion has globally Lipschitz coefficients with at most linear growth, so it cannot explode at a finite clock time. On a finite clock interval, $Y=ye^{\eta s}$ stays positive, $R$ stays bounded, and the integral defining $t(s)$ is finite. The original flow therefore cannot end, or take infinite physical time, at a finite clock value. This proves the claimed range of the clock and in particular the finiteness of every prescribed height-crossing time in the chosen direction. Integrating the bound $|d\log D/ds|\leq1$ gives the comparison.</p>

## Exact weighted moments {#section-weighted-moments}

<a id="tag-AXSH" data-assertion="theorem" data-title="The height-clock derivative martingale gives exact weighted moments for every real parameter"></a>
<p>Fix $b\in\mathbb R$ and set</p>
<div class="math-display">$$a=2b+\frac{\eta\kappa b(1-b)}2,
\qquad \lambda=4b+\frac{\eta\kappa b(1-2b)}2.$$</div>
<p>For $L\geq0$, put $h=ye^{\eta L}$ and let $T_h$ be the time at which $Y$ reaches $h$. Then</p>
<div class="math-display">$$\mathbb E\!\left[D_{T_h}^{a}\left(1+\frac{X_{T_h}^2}{h^2}\right)^b\right]
=\left(1+\frac{x^2}{y^2}\right)^b\left(\frac yh\right)^{\lambda-a}.$$</div>
<p><em>Proof.</em> Set $\psi_s=yD_{t(s)}/Y_{t(s)}$. By O0VQ, $d\log\psi_s/ds=-2\eta/(1+R_s^2)$. Consider</p>
<div class="math-display">$$M_s=\psi_s^a(1+R_s^2)^bY_{t(s)}^\lambda.$$</div>
<p>For $f(r)=(1+r^2)^b$, the drift divided by $\psi^aY^\lambda$ is</p>
<div class="math-display">$$\frac\kappa4(1+r^2)f''(r)-2\eta r f'(r)
+\eta\left(\lambda-\frac{2a}{1+r^2}\right)f(r)=0,$$</div>
<p>where the equality follows by substituting $a$ and $\lambda$. The remaining differential is</p>
<div class="math-display">$$\frac{dM_s}{M_s}
=\sqrt{2\kappa}\,b\frac{R_s}{\sqrt{1+R_s^2}}\,dW_s.$$</div>
<p>The stochastic coefficient has absolute value at most $\sqrt{2\kappa}|b|$. The exponential-martingale criterion therefore makes $M$ a true martingale on every bounded clock interval, for every real $b$. In particular $\mathbb E[M_L]=M_0=(1+x^2/y^2)^b y^\lambda$. Substituting $Y_{t(L)}=h$ gives the formula.</p>
<p>This proves the weighted height-crossing identity of Rohde–Schramm Theorem 3.2, with an arbitrary target height. The bounded stochastic coefficient is what justifies taking expectations; the vanishing drift alone would not suffice.</p>

## A direct fixed-time tail bound {#section-fixed-time-tail}

<a id="tag-M7AF" data-assertion="theorem" data-title="Inverse SLE derivatives satisfy a fixed-time power tail bound without a borderline logarithmic loss"></a>
<p>Let $0\leq b\leq1+4/\kappa$, and use $a,\lambda$ from AXSH with $\eta=1$. Put $q=\max\{a,\lambda\}$. For $0\leq T\leq1$, $0<y,\delta\leq1$ and $x\in\mathbb R$,</p>
<div class="math-display">$$\mathbb P\left(|\widehat f_T'(x+iy)|\geq\frac\delta y\right)
\leq 5^{(a-\lambda)_+/2}
\left(1+\frac{x^2}{y^2}\right)^b y^\lambda\delta^{-q}.$$</div>
<p><em>Proof.</em> By HHBC it suffices to work with reverse flow. Here $a\geq0$, and $Y_T^2\leq y^2+4T\leq5$, since $d(Y^2)/dt=4Y^2/|Z|^2\leq4$. The clock time $S_T=\log(Y_T/y)$ is a stopping time for the height-clock filtration: $\{S_T\leq s\}=\{t(s)\geq T\}$. It is bounded by $\frac12\log(1+4T/y^2)$. Optional stopping in AXSH therefore gives</p>
<div class="math-display">$$\mathbb E\!\left[y^aD_T^a(1+R_{S_T}^2)^bY_T^{\lambda-a}\right]
=\left(1+\frac{x^2}{y^2}\right)^b y^\lambda.$$</div>
<p>Assume first that $\delta>y$. Schwarz–Pick for the reverse map $H_T:\mathbb H\to\mathbb H$ gives $yD_T\leq Y_T$. On the event $D_T\geq\delta/y$, we therefore have $\delta\leq Y_T\leq\sqrt5$. Since $a,b\geq0$, the random variable inside this expectation is at least</p>
<div class="math-display">$$\delta^a\min_{\delta\leq v\leq\sqrt5}v^{\lambda-a}
=5^{-(a-\lambda)_+/2}\delta^{\max\{a,\lambda\}}.$$</div>
<p>Taking expectations proves the bound. If $\delta\leq y$, its right side is at least one: when $\lambda\geq a$ use $(y/\delta)^\lambda\geq1$, and when $a\geq\lambda$ use $y^\lambda\delta^{-a}\geq y^{\lambda-a}\geq1$.</p>
<p>For $a\ne\lambda$ this has the powers of Corollary 3.5. At $a=\lambda$ it removes the factor $1+|\log\delta|$ in that corollary. This is a stronger upper bound, not a correction of the source's valid statement.</p>

## Hölder continuity at each fixed time {#section-holder}

<a id="tag-OLNV" data-assertion="theorem" data-title="At each fixed time inverse SLE maps extend locally Hölder continuously for kappa different from four"></a>
<p>For every $\kappa>0$ with $\kappa\ne4$ there is $h(\kappa)>0$ such that, for each fixed $T>0$, almost surely $\widehat f_T$ extends to $\overline{\mathbb H}$ and is $h(\kappa)$-Hölder on every bounded subset. The exponents can be chosen so that</p>
<div class="math-display">$$\lim_{\kappa\downarrow0}h(\kappa)=\frac12,
\qquad \lim_{\kappa\to\infty}h(\kappa)=1.$$</div>
<p>More generally, for any $b$ in the range of M7AF with $\lambda>1+2b$, every exponent</p>
<div class="math-display">$$0<h<\frac{\lambda-1-2b}{\max\{a,\lambda\}}$$</div>
<p>has the asserted fixed-time Hölder property.</p>
<p><em>Proof.</em> First fix $0<T\leq1$ and a bounded horizontal interval. At height $y_n=2^{-n}$ use grid points $j y_n+i y_n$ spanning a slightly larger interval. Their number is $O(2^n)$ and $1+j^2=O(2^{2n})$. M7AF with $\delta=y_n^h$ gives</p>
<div class="math-display">$$\sum_n\sum_j\mathbb P\left(|\widehat f_T'(j y_n+i y_n)|\geq y_n^{h-1}\right)
\leq C\sum_n2^{-n(\lambda-1-2b-hq)}<\infty.$$</div>
<p>Borel–Cantelli gives a finite random constant bounding all grid derivatives by $C y_n^{h-1}$. Every point in the intervening dyadic strip is at bounded hyperbolic distance from one of these grid points. Koebe distortion for the univalent map $\widehat f_T$ therefore gives</p>
<div class="math-display">$$|\widehat f_T'(u+iv)|\leq C v^{h-1},\qquad 0<v\leq1,$$</div>
<p>on the original interval. The finitely many exceptional grid points are absorbed into $C$.</p>
<p>To integrate this estimate, let two points have separation $d$. If $d$ is at most half their larger height, their joining segment stays at height at least $d$, giving an image distance at most $C d^h$. Otherwise join them by two vertical segments and a horizontal segment at height equal to the maximum of their heights and $d$. This height lies between $d$ and $2d$. The vertical integrals are bounded by $C\int_0^{2d}v^{h-1}dv$, and the horizontal integral by $C d^h$. Thus the same Hölder bound holds. Derivatives at heights bounded away from zero are bounded on compact rectangles and are included by enlarging $C$.</p>
<p>Since $0<h<1$, these bounds give a unique extension to the real boundary. A countable exhaustion by rectangles gives the assertion on every bounded set, for this fixed $T$. Brownian scaling handles any other fixed positive time.</p>
<p>For an explicit choice valid whenever $\kappa\ne4$, take $b=\kappa^{-1/2}$. It lies in the allowed range, and direct substitution gives</p>
<div class="math-display">$$\lambda-1-2b=\frac{(\sqrt\kappa-2)^2}{2\sqrt\kappa}>0,
\qquad a-\lambda=\frac12-\frac2{\sqrt\kappa}.$$</div>
<p>If $H(\kappa)=(\lambda-1-2b)/\max\{a,\lambda\}$, then $0<H(\kappa)<1$, $H(\kappa)\to1/2$ at zero, and $H(\kappa)\to1$ at infinity. Choosing $h(\kappa)=H(\kappa)[1-\kappa/(1+\kappa)^2]$ proves the stated limits while keeping the summability inequality strict.</p>
<p>This proves the fixed-time theorem, including the existence of positive exponents at $\kappa=8$. It does not yield a single event of Hölder regularity at every time or construct a jointly continuous trace.</p>

## Comparing derivatives at two physical times {#section-comparison-repair}

<p>In the proof of Lemma 3.3, p.893, immediately before (3.15), Rohde–Schramm compare the derivative at the reverse height-one time with the derivative at a later fixed reverse time as though it were increasing. The derivative need not be monotone.</p>
<p>For zero driving and $z=iy$, the reverse solution has $Y_t=\sqrt{y^2+4t}$ and $D_t=y/Y_t$. With $y=1/2$, height one is reached at $t=3/16$, where $D_t=1/2$; at time one, $D_1=1/\sqrt{17}<1/2$. The strict inequality persists for driving functions sufficiently close to zero, by continuous dependence of the flow and the transverse height crossing. Brownian motion has positive probability of lying in such a uniform neighborhood on a fixed interval, so the problem is not confined to a null deterministic path.</p>
<p>A bounded factor repairs this comparison. If height one is reached at time $s\leq C$, O0VQ and $Y_C^2\leq1+4(C-s)\leq1+4C$ imply, for every real $a$,</p>
<div class="math-display">$$D_C^a\geq(1+4C)^{-|a|/2}D_s^a.$$</div>
<p>This is enough for the passage from (3.14) to (3.15), whose unspecified positive constant can absorb the factor. It handles negative moment orders as well. The <a href="/errata/rohde-schramm-basic-sle-2005/#reverse-derivative-comparison">source correction is provisional</a>; the remainder of the lower-bound proof of Lemma 3.3 is not supplied here.</p>


## From fixed times to joint radial continuity {#section-joint-continuity-update}

<p>The <a href="/articles/sle-tip-continuity/">joint-continuity article</a> now uses M7AF on a deterministic time grid to prove radial convergence uniformly over compact time intervals when kappa is different from eight. Its conclusion concerns the moving tip map, not an extension jointly over every real boundary point. The deterministic hull-generation theorem and the full kappa-eight trace theorem remain separate. The fixed-time statements above are unchanged.</p>


## The lower-bound proof is supplied {#section-lower-bound-update}

<p><a href="/tag/7NGO/">7NGO</a> now proves the full fixed-time lower estimate of Lemma 3.3, for every real parameter below its stated threshold. Under the derivative-martingale change of measure, <a href="/tag/CUBE/">CUBE</a> bounds a fractional moment of the physical height-crossing time and a small exponential moment of the terminal ratio. These estimates replace the source's tube event. The passage to fixed physical time uses the bounded-factor comparison recorded above, including negative moment orders. The source lemma is unchanged, and the provisional erratum remains a local repair.</p>


## An explicit height-crossing kernel {#section-gaussian-kernel-update}

<p>The <a href="/articles/sle-height-crossing-kernel/">Gaussian height-crossing calculation</a> develops Remark 3.4. At one parameter value, FZJD turns the hyperbolic coordinate into Brownian motion under the derivative-weighted law. THQF removes the density to give the exact endpoint moment measure, for both forward and reverse flow. PDLI computes an exact reverse-flow moment equivalent as the initial height vanishes, including its Gamma constant and logarithmic factor. The time is the random height-one crossing; the fixed-time statements above and the provisional derivative-comparison repair are unchanged.</p>
