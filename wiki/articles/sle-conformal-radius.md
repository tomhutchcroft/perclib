---
{
  "id": "sle-conformal-radius",
  "title": "SLE and conformal radius",
  "subtitle": "An angular diffusion gives the exact moment threshold",
  "kind": "method",
  "category": "General theory",
  "summary": "Measuring Loewner time by the loss of conformal radius turns the angle into a killed diffusion. Its hypergeometric martingale gives the exact moments, and a positive eigenfunction proves sharpness at the critical exponent.",
  "context": [
    "The process here is ordinary chordal SLE, without force points or boundary conditioning.",
    "The proofs use the standard Loewner conformal-map theorem, local existence and uniqueness for stochastic differential equations, Brownian time change, Itô calculus and optional stopping. These foundational tools are explicit inputs.",
    "The argument concerns a fixed interior point. It does not prove existence of a continuous SLE trace, percolation scaling convergence or a Hausdorff-dimension theorem."
  ],
  "related": ["continuum-connection-densities", "planar-factorization"],
  "sourceIds": ["rohde-schramm-basic-sle-2005"],
  "aliases": ["SLE derivative moments", "angular lifetime", "conformal-radius moments"],
  "prototypeUses": []
}
---

## Time measured by conformal radius {#section-radius-clock}

<p>Fix $\kappa&gt;0$ and an interior point $z=x+iy$ of the upper half-plane. Ordinary chordal SLE is the Loewner flow</p>
<div class="math-display">$$\partial_tg_t(z)=\frac{2}{g_t(z)-\sqrt\kappa B_t},\qquad g_0(z)=z.$$</div>
<p>Write $Z_t=g_t(z)-\sqrt\kappa B_t=X_t+iY_t$, and let $\tau(z)$ be the maximal lifetime of this solution in the upper half-plane. Before $\tau(z)$, the conformal radius of the unexplored domain $D_t$ about $z$ is</p>
<div class="math-display">$$\rho_t=\frac{2Y_t}{|g_t'(z)|},\qquad \rho_0=2y.$$</div>

<a id="tag-LZCO" data-assertion="proposition" data-title="Logarithmic conformal-radius loss is the lifetime clock of an angular diffusion"></a>
<p>Set $s(t)=\log(\rho_0/\rho_t)$. In this time parameter, $\Theta_s=\arg Z_{t(s)}$ solves</p>
<div class="math-display">$$d\Theta_s=\frac{\sqrt\kappa}{2}\,dW_s+
\frac{\kappa-4}{4}\cot\Theta_s\,ds,\qquad 0&lt;\Theta_s&lt;\pi.$$</div>
<p>If $\zeta$ is its maximal lifetime in $(0,\pi)$, then</p>
<div class="math-display">$$\zeta=\lim_{t\uparrow\tau(z)}s(t),\qquad
\mathcal Z(z):=\lim_{t\uparrow\tau(z)}\frac{y|g_t'(z)|}{Y_t}=e^\zeta.$$</div>
<p>The limits are allowed to be infinite.</p>
<p><em>Proof.</em> The Loewner equation and its derivative give</p>
<div class="math-display">$$dX_t=\frac{2X_t}{|Z_t|^2}\,dt-\sqrt\kappa\,dB_t,
\qquad dY_t=-\frac{2Y_t}{|Z_t|^2}\,dt,
\qquad \partial_t\log|g_t'(z)|=-2\operatorname{Re}(Z_t^{-2}).$$</div>
<p>Subtracting $\partial_t\log Y_t$ from the last expression yields</p>
<div class="math-display">$$s'(t)=\frac{4Y_t^2}{|Z_t|^4}&gt;0.$$</div>
<p>Itô's formula for the argument gives drift $(\kappa-4)X_tY_t/|Z_t|^4$ and Brownian coefficient $\sqrt\kappa Y_t/|Z_t|^2$. The quadratic variation in the new clock is $\kappa s/4$, proving the diffusion equation by Brownian time change.</p>
<p>The clocks agree up to their maximal lifetimes. Indeed, if the new clock ended at a finite value while the angle stayed in a compact subinterval of $(0,\pi)$, then</p>
<div class="math-display">$$\frac{d\log Y}{ds}=-\frac1{2\sin^2\Theta_s},\qquad
\frac{dt}{ds}=\frac{Y^2}{4\sin^4\Theta_s}$$</div>
<p>would leave $Y$ positive and $t$ finite. The original Loewner solution would remain away from its singularity and extend further, a contradiction. Conversely the angular process cannot reach an endpoint while $t&lt;\tau(z)$, because $Y_t&gt;0$. Local uniqueness identifies it with the maximal diffusion in the interval. Finally, the defining identity $y|g_t'|/Y_t=e^{s(t)}$ proves the last assertion. The generator in the radius clock is</p>
<div class="math-display">$$\mathcal A=\frac\kappa8\frac{d^2}{d\theta^2}
+\frac{\kappa-4}{4}\cot\theta\frac d{d\theta}.$$</div>

## The exact moments {#section-exact-moments}

<a id="tag-K0WT" data-assertion="theorem" data-title="The inverse conformal radius has an explicit hypergeometric moment below its critical exponent"></a>
<p>Suppose $0&lt;\kappa&lt;8$ and put $\lambda=1-\kappa/8$. For every real $p&lt;\lambda$, define</p>
<div class="math-display">$$\alpha_\pm=\frac12-\frac2\kappa
\pm\frac{\sqrt{32p\kappa+(2\kappa-8)^2}}{4\kappa},\qquad
F_p(q)={}_2F_1(\alpha_-,\alpha_+;1/2;q).$$</div>
<p>When the discriminant is negative the two parameters are conjugate; either choice of square root gives the same function. Then $\zeta&lt;\infty$ almost surely, $\mathcal Z(z)&lt;\infty$ almost surely, and</p>
<div class="math-display">$$\mathbb E[\mathcal Z(z)^p]
=\frac{F_p\bigl(x^2/(x^2+y^2)\bigr)}{F_p(1)},\qquad
F_p(1)=\frac{\Gamma(1/2)\Gamma(4/\kappa-1/2)}
{\Gamma(1/2-\alpha_-)\Gamma(1/2-\alpha_+)}&gt;0.$$</div>
<p><em>Proof.</em> The parameters satisfy $\alpha_-+\alpha_+=1-4/\kappa$ and $\alpha_-\alpha_+=-2p/\kappa$. For $q=\cos^2\theta$, the hypergeometric equation therefore gives</p>
<div class="math-display">$$\mathcal A\bigl(F_p(\cos^2\theta)\bigr)+pF_p(\cos^2\theta)=0.$$</div>
<p>More explicitly, the left side is $\kappa/2$ times</p>
<div class="math-display">$$q(1-q)F_p''+
\left(\frac12-\left(2-\frac4\kappa\right)q\right)F_p'
+\frac{2p}{\kappa}F_p,$$</div>
<p>which vanishes. Thus $e^{p(s\wedge\zeta)}F_p(\cos^2\Theta_{s\wedge\zeta})$ is a local martingale, with the endpoint value interpreted as $F_p(1)$.</p>
<p>First take $0&lt;p&lt;\lambda$. Then $\alpha_-&lt;0&lt;\alpha_+&lt;1/2$. Euler's integral gives</p>
<div class="math-display">$$F_p(q)=\frac{1}{B(\alpha_+,1/2-\alpha_+)}
\int_0^1 t^{\alpha_+-1}(1-t)^{-\alpha_+-1/2}(1-qt)^{-\alpha_-}\,dt.$$</div>
<p>The integrand is positive and decreases as $q$ increases from zero to one. At one it is integrable because $1/2-\alpha_--\alpha_+=4/\kappa-1/2&gt;0$. Consequently</p>
<div class="math-display">$$0&lt;F_p(1)\leq F_p(q)\leq F_p(0)=1,\qquad 0\leq q\leq1.$$</div>
<p>This positive lower bound is the essential integrability step. Stop first on compact subintervals and at a fixed clock time $s$. Bounded convergence removes the compact stopping, since the martingale is bounded by $e^{ps}$ up to that time. Its constant expectation implies</p>
<div class="math-display">$$F_p(\cos^2\Theta_0)
\geq F_p(1)\,\mathbb E[e^{p(s\wedge\zeta)}].$$</div>
<p>Monotone convergence shows both $\zeta&lt;\infty$ almost surely and $\mathbb E[e^{p\zeta}]&lt;\infty$. The martingale is now dominated by the integrable variable $e^{p\zeta}$. Letting $s\to\infty$ gives the stated quotient.</p>
<p>For $p=0$, the identity is immediate. For $p&lt;0$, the hypergeometric series is still real, smooth for $q&lt;1$ and continuous at $q=1$. Gauss summation gives the displayed endpoint value. Its denominator is positive: if the two parameters are real, both are less than $1/2$; if they are nonreal, the gamma factors are conjugate and their product is a positive squared modulus. The same stopped local martingale is now uniformly bounded, because $e^{p(s\wedge\zeta)}\leq1$ and $F_p$ is bounded on $[0,1]$. We already know that $\zeta$ is finite. Bounded convergence proves the quotient for these negative moments as well. Euler's integral, Gauss summation and the ordinary gamma identities are the special-function inputs in this argument.</p>

## Why the threshold is sharp {#section-sharp-threshold}

<a id="tag-ILR6" data-assertion="theorem" data-title="The moment threshold is exactly one minus kappa over eight, and the radius vanishes for kappa at least eight"></a>
<p>For $0&lt;\kappa&lt;8$,</p>
<div class="math-display">$$\mathbb E[\mathcal Z(z)^p]=\infty\quad\text{for every }p\geq1-\kappa/8.$$</div>
<p>For $\kappa\geq8$, one has $\zeta=\infty$ and $\mathcal Z(z)=\infty$ almost surely. Its positive moments are infinite and its negative moments are zero; the zeroth moment is one.</p>
<p><em>Proof.</em> For $0&lt;\kappa&lt;8$ put $b=8/\kappa-1&gt;0$ and $h(\theta)=\sin^b\theta$. Differentiation gives</p>
<div class="math-display">$$\mathcal Ah=-\lambda h,\qquad \lambda=1-\kappa/8.$$</div>
<p>The function is positive inside the interval, at most one, and zero at its endpoints. Compact stopping followed by bounded convergence at each fixed time makes $e^{\lambda(s\wedge\zeta)}h(\Theta_{s\wedge\zeta})$ a martingale. Therefore</p>
<div class="math-display">$$\mathbb E[h(\Theta_s);\zeta&gt;s]=e^{-\lambda s}h(\Theta_0),\qquad
\mathbb P(\zeta&gt;s)\geq e^{-\lambda s}h(\Theta_0).$$</div>
<p>For $p&gt;0$, the tail identity $\mathbb E[e^{p\zeta}]=1+p\int_0^\infty e^{ps}\mathbb P(\zeta&gt;s)\,ds$ holds with infinite values allowed. The lower bound makes this integral diverge for $p\geq\lambda$, including equality. No division by a vanishing hypergeometric boundary value is used at the critical exponent.</p>
<p>For $\kappa\geq8$, a scale function for the angular diffusion has derivative</p>
<div class="math-display">$$S'(\theta)=\sin^{8/\kappa-2}\theta.$$</div>
<p>Its integrals diverge at both endpoints. To see directly why an endpoint cannot be reached, fix $0&lt;\theta&lt;c&lt;\pi$. Itô's formula for the scale function, stopped on $[\varepsilon,c]$, gives</p>
<div class="math-display">$$\mathbb P_\theta(T_\varepsilon&lt;T_c)
=\frac{S(c)-S(\theta)}{S(c)-S(\varepsilon)}\longrightarrow0
\quad\text{as }\varepsilon\downarrow0.$$</div>
<p>If a continuous path reached zero in finite time, some rational time before that visit would be followed by the visit without an intervening return to a fixed interior level. The Markov property and the last display give probability zero to each such event. Reflection handles the other endpoint. On compact subintervals the coefficients are regular, so no other finite explosion is possible. Thus $\zeta=\infty$, and LZCO gives the assertions about $\mathcal Z$.</p>

## Distance to the terminal boundary {#section-distance-exponent}

<a id="tag-DC8Q" data-assertion="corollary" data-title="The terminal boundary-distance exponent is one minus kappa over eight"></a>
<p>Let $d_* =\lim_{t\uparrow\tau(z)}\operatorname{dist}(z,\partial D_t)$. For every $\kappa&gt;0$,</p>
<div class="math-display">$$\frac{y}{2\mathcal Z(z)}\leq d_*\leq\frac{2y}{\mathcal Z(z)}.$$</div>
<p>For $0&lt;\kappa&lt;8$, put $\lambda=1-\kappa/8$, $b=8/\kappa-1$ and $\theta=\arg z$. For $0&lt;\varepsilon&lt;y/2$ and $0&lt;p&lt;\lambda$,</p>
<div class="math-display">$$\sin^b\theta\left(\frac{\varepsilon}{2y}\right)^\lambda
\leq\mathbb P(d_*&lt;\varepsilon)
\leq\mathbb E[\mathcal Z(z)^p]\left(\frac{2\varepsilon}{y}\right)^p.$$</div>
<p>In particular $d_*&gt;0$ almost surely and</p>
<div class="math-display">$$\lim_{\varepsilon\downarrow0}
\frac{\log\mathbb P(d_*&lt;\varepsilon)}{\log(\varepsilon/y)}
=1-\kappa/8.$$</div>
<p>For $\kappa\geq8$, $d_*=0$ almost surely.</p>
<p><em>Proof.</em> The conformal-radius form of Koebe's theorem says $\rho_t/4\leq\operatorname{dist}(z,\partial D_t)\leq\rho_t$. Since $\rho_t\downarrow2y/\mathcal Z(z)$, this proves the first display. The lower tail bound in ILR6 gives $\mathbb P(\mathcal Z&gt;R)\geq\sin^b\theta\,R^{-\lambda}$ for $R\geq1$. Apply it with $R=2y/\varepsilon$ for the lower bound. For the upper bound, $d_*&lt;\varepsilon$ requires $\mathcal Z&gt;y/(2\varepsilon)$; use Markov's inequality and K0WT. Taking logarithms and then letting $p\uparrow\lambda$ gives the limit. The almost-sure statements follow from K0WT and ILR6.</p>
<p>This formulation only uses Loewner domains. Relating $d_*$ to distance from the full trace uses the trace and hull geometry established elsewhere in Rohde–Schramm; no continuous-trace theorem is proved here. At $\kappa=6$ the threshold is $1/4$, strictly above $5/48$. The <a href="/articles/continuum-connection-densities/#section-conditioned-moment">conditioned moment bound GXMS</a> still needs its separate percolation comparison: none of the ordinary-SLE calculations changes measure to a force-point law.</p>


<p>The <a href="/articles/sle-swallowing/#section-finite-lifetime">physical-time argument</a> now proves that every fixed nonzero point has finite Loewner lifetime when $\kappa&gt;4$. Its clock is different from the logarithmic radius clock: for $4&lt;\kappa&lt;8$, finite physical lifetime is compatible with the positive terminal conformal radius proved above. The same article derives a beta law for simultaneous swallowing of two boundary points.</p>
