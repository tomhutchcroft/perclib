---
{
  "id": "mixed-sle-forces",
  "title": "Interior forces in half-plane and strip coordinates",
  "subtitle": "Real parts of the force field, target admissibility and the two strip ends",
  "kind": "method",
  "category": "General theory",
  "summary": "A complex force point contributes the real part of the half-plane or strip vector field to the driver. This observation extends the coordinate-change proof to mixed configurations and gives the two endpoint forces in chordal or radial coordinates.",
  "context": [
    "Kappa is nonnegative and force weights are arbitrary real numbers. Finite initial force points differ from the initial driver; coincident force weights are combined.",
    "The deterministic normalizations and clocks are supplied by C6T0 and 1AUW. The remaining argument uses Itô calculus, Brownian time change and local SDE uniqueness.",
    "Every law is stopped before force collision or swallowing of the new target. A half-plane destination requires a finite image of the starting point."
  ],
  "related": ["sle-coordinate-changes", "strip-sle", "chordal-radial-sle", "sle-force-martingales"],
  "sourceIds": ["schramm-wilson-coordinate-changes-2005"],
  "aliases": ["mixed strip forces", "interior chordal forces", "dipolar radial coordinates"],
  "prototypeUses": []
}
---

## Complex marks under a real Möbius map {#section-half-plane-forces}

<p>For marks $V^j\in\overline{\mathbb H}\cup\{\infty\}$, the chordal force system is</p>
<div class="math-display">$$dU_t=\sqrt\kappa\,dB_t+
\sum_j\rho_j\operatorname{Re}\frac1{U_t-V_t^j}\,dt,\qquad
dV_t^j=\frac2{V_t^j-U_t}\,dt.$$</div>
<p>A mark at infinity stays there and contributes zero to the driver. Let $m:\mathbb H\to\mathbb H$ be a real Möbius map with $m(U_0)$ finite. Write $p=m^{-1}(\infty)$ and use the normalization $\varphi_t$ and clock $s$ from <a href="/articles/sle-coordinate-changes/#section-target-normalization">C6T0</a>.</p>

<a id="tag-C1GN" data-assertion="theorem" data-title="A real Möbius map transports mixed chordal forces and the compensating old-target weight"></a>
<p>Up to force collision or swallowing $p$, the image hulls have chordal force-point law with the same weights at $m(V_0^j)$ and an additional force of weight</p>
<div class="math-display">$$\Delta=\kappa-6-\sum_j\rho_j$$</div>
<p>at $m(\infty)$. Existing weights there are combined. In the evolving coordinates, the marks are $\widehat V_{s(t)}^j=\varphi_t(V_t^j)$ and the driver is $\widehat U_{s(t)}=\varphi_t(U_t)$. If $\Delta=0$, the original weights suffice.</p>
<p><em>Proof.</em> Put $a_t=\varphi_t'(U_t)>0$ and $b_t=\varphi_t''(U_t)$, so $s'(t)=a_t^2$. The fractional-linear identity</p>
<div class="math-display">$$\frac{\varphi_t'(U_t)}{U_t-v}
=\frac{\varphi_t'(U_t)^2}{\varphi_t(U_t)-\varphi_t(v)}
-\frac12\varphi_t''(U_t)$$</div>
<p>holds for complex $v$ as well as real $v$. Indeed, substitution of $\varphi(z)=c-d/(z-P)$ proves it as a rational identity; the affine case is immediate. Taking real parts is legitimate because $a_t$ and $b_t$ are real. Limits cover a mark at infinity or at the pole.</p>
<p>The coefficients of $\varphi_t$ have finite variation and $(\partial_t\varphi_t)(U_t)=-3b_t$ by C6T0. Itô's formula therefore gives</p>
<div class="math-display">$$d\widehat U_{s(t)}
=a_t\sqrt\kappa\,dB_t+
\left(a_t^2\sum_j\rho_j\operatorname{Re}
\frac1{\widehat U_{s(t)}-\widehat V_{s(t)}^j}
+\frac{\Delta b_t}{2}\right)dt.$$</div>
<p>For the nonaffine map, $b_t/2=a_t^2/(\widehat U_{s(t)}-\varphi_t(\infty))$. In the affine case both sides are zero under the convention at infinity. Thus the remaining drift is exactly the force at the old target's image.</p>
<p>The rational vector-field identity of C6T0 holds throughout $\mathbb H$, so the chain rule gives</p>
<div class="math-display">$$d\varphi_t(V_t^j)=
\frac{2a_t^2}{\varphi_t(V_t^j)-\varphi_t(U_t)}\,dt.$$</div>
<p>Its limiting forms treat marks at the pole and at infinity. The old-target image follows the same equation. Finally, $\widehat B_s=\int_0^{t(s)}a_r\,dB_r$ has quadratic variation $s$. Dividing by the clock rate gives the claimed mixed-force system. On compact stops its coefficients are locally Lipschitz away from collisions; uniqueness and exhaustion give the law up to the stated stop.</p>

## Interior marks in the strip {#section-strip-mixed}

<p>Let $S=\{z:0<\operatorname{Im}z<\pi/2\}$. For finite marks in $\overline S$, the strip force equations are</p>
<div class="math-display">$$dW_t=\sqrt\kappa\,dB_t+
\sum_j\rho_j\operatorname{Re}\coth(W_t-V_t^j)\,dt,\qquad
dV_t^j=2\coth(V_t^j-W_t)\,dt.$$</div>
<p>These are the reflected-force convention of Schramm–Wilson, Definition 5: for real $W$, the average of $\coth(W-V)$ and $\coth(W-\overline V)$ is its real part. On the lower and upper boundaries this reduces to $\coth$ and $\tanh$, respectively. The ends stay fixed and contribute $+\rho$ at $-\infty$ and $-\rho$ at $+\infty$.</p>

<a id="tag-P3E9" data-assertion="theorem" data-title="The exponential strip normalization transports balanced mixed forces to the half-plane"></a>
<p>Suppose $\sum_j\rho_j=\kappa-6$. Under $E(z)=e^{2z}$, the strip hulls have chordal force-point law with the same weights, in the clock</p>
<div class="math-display">$$Y_t=e^{2W_t-4t},\qquad b_t=-8\int_0^tY_r\,dr,\qquad
s(t)=4\int_0^tY_r^2\,dr.$$</div>
<p>The transformed driver and marks are</p>
<div class="math-display">$$\widehat U_{s(t)}=Y_t+b_t,\qquad
\widehat V_{s(t)}^j=e^{2V_t^j-4t}+b_t.$$</div>
<p>The endpoint values are $b_t$ and infinity. This law is stopped before force collision.</p>
<p><em>Proof.</em> The deterministic normalization in <a href="/articles/strip-sle/#section-exponential-normalization">1AUW</a> is valid at interior points as well as boundary points. For every finite mark,</p>
<div class="math-display">$$\operatorname{Re}\coth(W_t-V_t^j)
=2Y_t\operatorname{Re}
\frac1{\widehat U_{s(t)}-\widehat V_{s(t)}^j}-1.$$</div>
<p>This follows from $\coth(W-V)=(e^{2W}+e^{2V})/(e^{2W}-e^{2V})$; taking limits gives the endpoint identities. Itô's formula for $Y_t$, followed by $b_t'=-8Y_t$, yields</p>
<div class="math-display">$$d\widehat U_{s(t)}
=2Y_t\sqrt\kappa\,dB_t+
\left(4Y_t^2\sum_j\rho_j\operatorname{Re}
\frac1{\widehat U_{s(t)}-\widehat V_{s(t)}^j}
+2Y_t\left(\kappa-6-\sum_j\rho_j\right)\right)dt.$$</div>
<p>The last term vanishes. For $Z_t^j=e^{2V_t^j-4t}$, differentiation gives</p>
<div class="math-display">$$\frac{d}{dt}(Z_t^j+b_t)
=-4Z_t^j+4Z_t^j\frac{Z_t^j+Y_t}{Z_t^j-Y_t}-8Y_t
=\frac{8Y_t^2}{Z_t^j-Y_t}.$$</div>
<p>Thus every transformed mark has the chordal evolution after division by $s'=4Y^2$. At the left end this is $b'=-8Y$; the right end remains at infinity. The process $\int_0^{t(s)}2Y_r\,dB_r$ is Brownian in the new clock. Local uniqueness completes the argument. On compact stops $Y$ is positive and bounded above and below, so no extra finite stopping time is introduced by the exponential chart.</p>

## The two ends in chordal and radial coordinates {#section-strip-targets}

<a id="tag-8GVO" data-assertion="corollary" data-title="A mixed strip process acquires equal endpoint forces in a half-plane or disk destination"></a>
<p>Let $\psi:S\to X$ be a conformal bijection, where $X=\mathbb H$ or $\mathbb D$. In the half-plane case require $\psi(W_0)$ finite. For arbitrary mixed strip weights, put $\Delta=\kappa-6-\sum_j\rho_j$. The image law, in the destination's capacity time, has the original weights at the image marks and additional weights $\Delta/2$ at each of $\psi(-\infty)$ and $\psi(+\infty)$.</p>
<p>The law is identified up to force collision or swallowing of $\psi^{-1}(o_X)$, where $o_{\mathbb H}=\infty$ and $o_{\mathbb D}=0$. Existing endpoint weights are combined, and a force at the destination target has zero drift.</p>
<p><em>Proof.</em> Add weight $\Delta/2$ at both strip ends. Their constant contributions to the original driving drift cancel, and the total weight becomes $\kappa-6$. P3E9 therefore sends this unchanged process to a balanced chordal law under $E$.</p>
<p>Write $\psi=m\circ E$. If $X=\mathbb H$, apply C1GN to $m$; balance makes its extra old-target weight zero. If $X=\mathbb D$, apply <a href="/articles/chordal-radial-sle/#section-mixed-force-change">5KL5</a>, again with no extra weight. The deterministic normalized maps compose, so the resulting time is the destination capacity time. The only new stop is swallowing the preimage of its target. Exhausting compact stops gives exactly the stated lifetime.</p>
<p>In particular, ordinary dipolar SLE has two endpoint weights $(\kappa-6)/2$ in either destination. Their occurrence is determined by cancellation in the strip, not by a choice of how to distribute a single force in the destination.</p>

## Admissibility of the starting point {#section-starting-image}

<p>The finite-image hypothesis for a half-plane destination is necessary under the source's Definition 2, which excludes a driver started at infinity. Theorem 3 does not state this destination condition explicitly. For example, take $\kappa=6$, $U_0=0$, no force points and $m(z)=-1/z$. The weight balance holds and the starting point is admissible in the original half-plane, but its image is infinity. The claimed destination process is not defined by Definition 2, and the proposed new-target stop starts at zero.</p>
<p>The corrected scope requires $\psi(w_0)\ne\infty$ when the destination is $\mathbb H$, equivalently that its new target differ from the starting point. Section 4 already includes this condition in its strip-to-half-plane assertion. C1GN and 8GVO state it explicitly, as do the preceding half-plane normalization and radial-to-chordal proof. This <a href="/errata/schramm-wilson-coordinate-changes-2005/#finite-starting-image">provisional erratum</a> concerns admissibility; it does not change the force balance or the proof on admissible configurations.</p>

