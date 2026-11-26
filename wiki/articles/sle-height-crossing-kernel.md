---
{
  "id": "sle-height-crossing-kernel",
  "title": "A Gaussian formula for SLE height crossings",
  "subtitle": "A change of measure removes the ratio drift",
  "kind": "method",
  "category": "General theory",
  "summary": "At one derivative-moment order, the hyperbolic coordinate of the centered Loewner flow becomes Brownian motion under a weighted law. Its Gaussian density gives the exact endpoint moment measure and a logarithmic asymptotic for reverse flow.",
  "context": [
    "The flow runs until the image of one fixed point reaches height one. This is a random physical time, with a deterministic logarithmic height interval.",
    "The proof uses the height-clock diffusion O0VQ, the true derivative martingale AXSH and Girsanov's theorem. It applies in both flow directions for every positive kappa, without assuming trace existence.",
    "The explicit kernel develops Rohde–Schramm Remark 3.4. The moment asymptotic is derived here from that kernel; no occupation-time tail estimate or fixed-physical-time equivalent is asserted."
  ],
  "related": ["sle-derivative-estimates", "sle-derivative-lower-bounds", "sle-whitney-sums"],
  "sourceIds": ["rohde-schramm-basic-sle-2005"],
  "aliases": ["Gaussian SLE derivative kernel", "Brownian height-crossing tilt"],
  "prototypeUses": []
}
---

## Removing the hyperbolic drift {#section-brownian-law}

<p>Fix $\kappa>0$ and $z=x+iy\in\mathbb H$ with $y\ne1$. Choose $\eta=1$ when $y<1$ and $\eta=-1$ when $y>1$, and run</p>
<div class="math-display">$$\partial_tH_t^\eta(z)=-\frac{2\eta}{H_t^\eta(z)-U_t},
\qquad U_t=\sqrt\kappa B_t,\qquad H_0^\eta(z)=z.$$</div>
<p>Write $H_t^\eta(z)-U_t=X_t+iY_t$ and $D_t=|(H_t^\eta)'(z)|$. Thus the reverse flow raises the height and the forward flow lowers it. Let $\tau$ be the first time $Y_t=1$. In $D_\tau$ the spatial derivative is taken at fixed time and then evaluated at $\tau$.</p>
<p>By <a href="/tag/O0VQ/">O0VQ</a>, $\tau$ is finite and, in forward flow, precedes the lifetime of $z$. Use the clock and coordinates</p>
<div class="math-display">$$s=\eta\log(Y_t/y),\qquad L=|\log y|,\qquad
R_s=\frac{X_{t(s)}}{Y_{t(s)}},\qquad V_s=\operatorname{arsinh}R_s,\qquad
v=\operatorname{arsinh}(x/y).$$</div>
<p>Set</p>
<div class="math-display">$$b_*=\frac14+\frac{2\eta}{\kappa},\qquad
a_*=2b_*+\frac{\eta\kappa b_*(1-b_*)}{2},\qquad
\lambda_*=4b_*+\frac{\eta\kappa b_*(1-2b_*)}{2}.$$</div>

<a id="tag-FZJD" data-assertion="proposition" data-title="The special derivative tilt makes the hyperbolic height coordinate Brownian in either flow direction"></a>
<p>On the height-clock filtration up to $L$, define $\mathbb Q$ by</p>
<div class="math-display">$$\frac{d\mathbb Q}{d\mathbb P}=\frac{M_L}{M_0},
\qquad
M_s=\left(\frac{yD_{t(s)}}{Y_{t(s)}}\right)^{a_*}
\cosh^{2b_*}(V_s)\,Y_{t(s)}^{\lambda_*}.$$</div>
<p>Then under $\mathbb Q$ the whole path has the representation</p>
<div class="math-display">$$V_s=v+\sqrt{\kappa/2}\,\widetilde B_s,\qquad 0\le s\le L,$$</div>
<p>where $\widetilde B$ is standard Brownian motion. In particular, the normalized derivative and the physical crossing time are the Brownian functionals</p>
<div class="math-display">$$\frac{yD_\tau}{Y_\tau}
=\exp\left\{-2\eta\int_0^L\operatorname{sech}^2(V_s)\,ds\right\},
\qquad
\tau=\frac{y^2}{2}\int_0^L e^{2\eta s}\cosh^2(V_s)\,ds.$$</div>
<p><em>Proof.</em> Applying Itô's formula to the ratio diffusion in O0VQ gives</p>
<div class="math-display">$$dV_s=\sqrt{\kappa/2}\,dW_s
-\left(2\eta+\frac\kappa4\right)\tanh(V_s)\,ds.$$</div>
<p>The martingale <a href="/tag/AXSH/">AXSH</a> has stochastic coefficient $\sqrt{2\kappa}\,b_*\tanh(V_s)$, which is bounded even when $b_*<0$. It is a positive true martingale on $[0,L]$, so the displayed density defines a probability law. Girsanov adds $\kappa b_*\tanh(V_s)$ to the drift. The choice of $b_*$ cancels the drift exactly, proving the Brownian representation. Integrating $d\log(yD/Y)/ds=-2\eta/(1+R_s^2)$ and $dt/ds=Y^2(1+R_s^2)/2$ gives the two functionals.</p>

## The endpoint moment measure {#section-endpoint-density}

<a id="tag-THQF" data-assertion="theorem" data-title="The derivative-weighted endpoint at height one has an explicit Gaussian hyperbolic density"></a>
<p>For every Borel set $A\subseteq\mathbb R$,</p>
<div class="math-display">$$
\mathbb E\!\left[D_\tau^{a_*}\mathbf1_{\{X_\tau\in A\}}\right]
=\frac{\cosh^{2b_*}(v)\,y^{\lambda_*-a_*}}{\sqrt{\pi\kappa L}}
\int_A
\frac{\exp\!\left\{-\dfrac{(\operatorname{arsinh}u-v)^2}{\kappa L}\right\}}
{(1+u^2)^{b_*+1/2}}\,du.
$$</div>
<p>This is a finite weighted measure; its total mass is $\mathbb E[D_\tau^{a_*}]$, not generally one.</p>
<p><em>Proof.</em> At height one, $X_\tau=\sinh V_L$, while</p>
<div class="math-display">$$M_L=y^{a_*}D_\tau^{a_*}\cosh^{2b_*}V_L,\qquad
M_0=\cosh^{2b_*}(v)y^{\lambda_*}.$$</div>
<p>Removing the density therefore gives</p>
<div class="math-display">$$
\mathbb E\!\left[D_\tau^{a_*}\mathbf1_{\{X_\tau\in A\}}\right]
=\cosh^{2b_*}(v)y^{\lambda_*-a_*}
\mathbb E_{\mathbb Q}\!\left[
\cosh^{-2b_*}(V_L)\mathbf1_{\{\sinh V_L\in A\}}\right].
$$</div>
<p>Under $\mathbb Q$, $V_L$ is Gaussian with mean $v$ and variance $\kappa L/2$. Substitute its density and change variables $u=\sinh w$, so $dw=du/\sqrt{1+u^2}$. This is the stated formula. In the $w$ variable the extra factor $\cosh^{-2b_*}w$ grows at most exponentially, so its Gaussian integral is finite for either sign of $b_*$.</p>
<p>The excluded case $y=1$ has $\tau=0$, $D_\tau=1$ and $X_\tau=x$; its endpoint measure is the point mass at $x$.</p>

## The reverse-flow moment as the starting height vanishes {#section-moment-asymptotic}

<p>For reverse flow, the parameters simplify to</p>
<div class="math-display">$$b_*=\frac14+\frac2\kappa>0,\qquad
a_*=1+\frac2\kappa+\frac{3\kappa}{32},\qquad
\lambda_*=1+\frac4\kappa+\frac{\kappa}{16}
=\frac{(\kappa+8)^2}{16\kappa}.$$</div>

<a id="tag-PDLI" data-assertion="corollary" data-title="The reverse height-crossing derivative moment has an explicit inverse square-root logarithmic asymptotic"></a>
<p>Start the reverse flow at $iy$, $0<y<1$, and let $\tau_y$ be its height-one time. As $y\downarrow0$,</p>
<div class="math-display">$$
\mathbb E\!\left[|(H_{\tau_y}^{1})'(iy)|^{a_*}\right]
\sim
\frac{\Gamma(b_*)}{\sqrt\kappa\,\Gamma(b_*+1/2)}
\frac{y^{\,2/\kappa-\kappa/32}}{\sqrt{\log(1/y)}}.
$$</div>
<p><em>Proof.</em> In THQF take $x=0$ and $A=\mathbb R$. After factoring out $y^{\lambda_*-a_*}/\sqrt{\pi\kappa\log(1/y)}$, the remaining integral tends to</p>
<div class="math-display">$$
\int_{\mathbb R}(1+u^2)^{-b_*-1/2}\,du
=\frac{\sqrt\pi\,\Gamma(b_*)}{\Gamma(b_*+1/2)}.
$$</div>
<p>Indeed, the Gaussian factor tends pointwise to one and is bounded by one; the displayed weight is integrable because $b_*>0$. The integral is the beta integral after substituting $t=u^2$ on the positive half-line. Finally $\lambda_*-a_*=2/\kappa-\kappa/32$.</p>
<p>For example, at $\kappa=8$ this gives $a_*=\lambda_*=2$ and a moment asymptotic $\sqrt{\pi/8}/\sqrt{\log(1/y)}$. The crossing time still depends on $y$ and on the flow. Fixed-time inverse-map estimates require a separate comparison; this calculation also does not supply the trace construction at $\kappa=8$.</p>
