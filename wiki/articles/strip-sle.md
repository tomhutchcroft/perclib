---
{
  "id": "strip-sle",
  "title": "From strip SLE to chordal SLE",
  "subtitle": "An exponential map, capacity time and the two ends of the strip",
  "kind": "method",
  "category": "General theory",
  "summary": "Exponentiating the strip Loewner equation gives an explicit chordal normalization. The change in its driving drift explains the force-weight balance and the endpoint forces of dipolar SLE.",
  "context": [
    "The strip has height pi/2. The driver starts on its lower boundary; force points may lie on either boundary or at either end.",
    "The argument uses deterministic Loewner conformal maps, local SDE uniqueness, Itô calculus and Brownian time change. All laws are stopped before a force collision or swallowing of a new target.",
    "Only boundary forces are treated here. Interior-force coordinate changes and terminal trace statements are separate questions."
  ],
  "related": ["sle-coordinate-changes", "sle-force-martingales", "continuum-connection-densities"],
  "sourceIds": ["schramm-wilson-coordinate-changes-2005"],
  "aliases": ["dipolar SLE", "strip Loewner equation", "dipolar endpoint forces"],
  "prototypeUses": []
}
---

## Exponentiating the Loewner equation {#section-exponential-normalization}

<p>Write $S=\{z:0&lt;\operatorname{Im}z&lt;\pi/2\}$ and $E(z)=e^{2z}$. For a continuous real driver $W$, let $g_t:S\setminus K_t\to S$ be the strip Loewner maps, satisfying</p>
<div class="math-display">$$\partial_tg_t(z)=2\coth(g_t(z)-W_t),\qquad g_0(z)=z.$$</div>
<p>We work on compact time intervals on which these maps are defined. The strip ends are fixed as prime ends. The basic deterministic Loewner conformal-map theorem is used throughout.</p>

<a id="tag-1AUW" data-assertion="proposition" data-title="Exponentiation gives an explicit hydrodynamic normalization and capacity clock for strip hulls"></a>
<p>Put</p>
<div class="math-display">$$Y_t=e^{2W_t-4t},\qquad
b_t=-8\int_0^tY_r\,dr,\qquad
s(t)=4\int_0^tY_r^2\,dr.$$</div>
<p>In the strictly increasing clock $s$, the maps</p>
<div class="math-display">$$\widehat g_{s(t)}(z)=e^{-4t+2g_t((\log z)/2)}+b_t,\qquad
\widehat U_{s(t)}=Y_t+b_t$$</div>
<p>are the hydrodynamically normalized chordal Loewner maps of $E(K_t)$. Here $0&lt;\operatorname{Im}\log z&lt;\pi$. The two strip ends map to the boundary marks $b_t$ and $\infty$.</p>
<p><em>Proof.</em> Set $Z=e^{-4t+2g_t((\log z)/2)}$. Since $\coth(g_t-W_t)=(Z+Y_t)/(Z-Y_t)$, differentiation at fixed $z$ gives</p>
<div class="math-display">$$\partial_t(Z+b_t)
=-4Z+4Z\frac{Z+Y_t}{Z-Y_t}-8Y_t
=\frac{8Y_t^2}{Z-Y_t}.
$$</div>
<p>The initial map is the identity, and $Z-Y_t=\widehat g_{s(t)}(z)-\widehat U_{s(t)}$. Dividing by $s'(t)=4Y_t^2$ gives the chordal equation. The displayed map is conformal from the complement of $E(K_t)$ onto $\mathbb H$. Uniqueness of the Loewner ODE identifies it with the chordal map driven by $\widehat U$, whose expansion is $z+2s/z+O(z^{-2})$. In particular the clock is derived from the equation. The limits as the strip coordinate tends to $-\infty$ and $+\infty$ give $b_t$ and $\infty$ respectively. On each compact interval $Y$ is positive and bounded above and below, so the change of clock and its inverse are well defined.</p>

## Transporting the forces {#section-strip-forces}

<p>For finite boundary marks $V^j$, strip SLE is the stopped system</p>
<div class="math-display">$$dW_t=\sqrt\kappa\,dB_t+
\sum_j\rho_j\coth(W_t-V_t^j)\,dt,
\qquad dV_t^j=2\coth(V_t^j-W_t)\,dt.$$</div>
<p>A mark on the upper boundary remains on that boundary. Its contribution to the driver is real, since $\coth(x-i\pi/2)=\tanh x$. Marks at the two ends stay there; their respective contributions are $+\rho_j$ at $-\infty$ and $-\rho_j$ at $+\infty$. The initial driver differs from every finite mark.</p>

<a id="tag-YEJS" data-assertion="theorem" data-title="Balanced boundary forces turn strip SLE into chordal SLE under a conformal map"></a>
<p>Let $\kappa\geq0$ and $\sum_j\rho_j=\kappa-6$. Under $E$, the strip hulls have chordal $\operatorname{SLE}_\kappa(\rho_1,\ldots,\rho_n)$ law in the clock of 1AUW, with marks</p>
<div class="math-display">$$\widehat V_{s(t)}^j=e^{-4t+2V_t^j}+b_t.$$</div>
<p>The formula is interpreted as $b_t$ at the left end and $\infty$ at the right end. More generally, the same conclusion holds for any conformal bijection $\psi:S\to\mathbb H$ with $\psi(W_0)$ finite, stopped before force collision or swallowing of $\psi^{-1}(\infty)$.</p>
<p><em>Proof.</em> For each finite mark,</p>
<div class="math-display">$$\coth(W_t-V_t^j)=
\frac{2Y_t}{\widehat U_{s(t)}-\widehat V_{s(t)}^j}-1.
$$</div>
<p>This identity also holds at either end by limits, with zero reciprocal at infinity. Itô's formula and $b_t'=-8Y_t$ now give</p>
<div class="math-display">$$d\widehat U_{s(t)}=2Y_t\sqrt\kappa\,dB_t+
\left(4Y_t^2\sum_j\frac{\rho_j}{\widehat U_{s(t)}-\widehat V_{s(t)}^j}
+2Y_t\left(\kappa-6-\sum_j\rho_j\right)\right)dt.$$</div>
<p>The balance cancels the last term. Also, the calculation in 1AUW, applied at each mark, gives</p>
<div class="math-display">$$d\widehat V_{s(t)}^j=
\frac{8Y_t^2}{\widehat V_{s(t)}^j-\widehat U_{s(t)}}\,dt.$$</div>
<p>At the left end this says $b_t'=-8Y_t$; the right end is fixed. The process $\widehat B_s=\int_0^{t(s)}2Y_r\,dB_r$ has quadratic variation $s$. Thus division by $s'(t)$ gives the chordal force equations with Brownian driver in the new clock. Local uniqueness identifies the stopped laws.</p>
<p>Finally write $\psi=m\circ E$ with $m$ a real Möbius automorphism of $\mathbb H$. All transformed marks lie on its extended real boundary, so <a href="/articles/sle-coordinate-changes/#section-force-covariance">6RZ1</a> applies with the same balanced weights. Its new-target stopping restriction gives the one in the statement. Neither step extends the law past a collision.</p>

## The endpoint forces of dipolar SLE {#section-dipolar-endpoints}

<a id="tag-EKFY" data-assertion="corollary" data-title="An unbalanced strip process acquires equal compensating forces at the two strip ends"></a>
<p>For arbitrary boundary weights, put $\Delta=\kappa-6-\sum_j\rho_j$. The image under $\psi:S\to\mathbb H$ has the original forces and two additional forces of weight $\Delta/2$, at $\psi(-\infty)$ and $\psi(+\infty)$, under the stops in YEJS. Existing forces at these marks are combined. In particular ordinary dipolar SLE has two endpoint weights $(\kappa-6)/2$ in chordal coordinates.</p>
<p><em>Proof.</em> Add a force of weight $\Delta/2$ at each strip end. Their contributions to $dW$ cancel, while the sum of the weights becomes $\kappa-6$. Apply YEJS. Under $E$, the endpoint marks start at $0$ and $\infty$; the latter has zero chordal drift. Thus the unbalanced drift left in the proof of YEJS is exactly the force $(\Delta/2)/(\widehat U-b)$ after division by the clock rate.</p>
<p>For example, at $\kappa=0$ the force-free strip driver can be $W_t=0$. Then $Y_t=e^{-4t}$, $b_t=-2(1-e^{-4t})$, $s(t)=(1-e^{-8t})/2$ and $\widehat U_{s(t)}=3e^{-4t}-2$. Consequently $d\widehat U/ds=-3/(\widehat U-b)$, as predicted by the endpoint weight $-3$. The finite total clock in this example does not assert any extension through its terminal time.</p>
