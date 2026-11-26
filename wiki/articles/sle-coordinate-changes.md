---
{
  "id": "sle-coordinate-changes",
  "title": "Changing the target of chordal SLE",
  "subtitle": "Möbius normalization, capacity time and force weights",
  "kind": "method",
  "category": "General theory",
  "summary": "The boundary derivatives of a Loewner map determine its normalization after a Möbius change of target. The resulting Itô correction explains the force-weight balance and transfers bulk martingales between coordinates.",
  "context": [
    "The maps here are real Möbius automorphisms of the upper half-plane, and all force points lie on its extended real boundary.",
    "The proofs use the basic deterministic Loewner conformal-map theorem, analytic continuation at an unswallowed real point, local SDE uniqueness, Itô calculus and Brownian time change.",
    "Every change is stopped before a force-point collision or swallowing of the new target. No radial, strip or terminal trace theorem is asserted."
  ],
  "related": ["continuum-connection-densities", "sle-conformal-radius", "sle-swallowing"],
  "sourceIds": ["schramm-wilson-coordinate-changes-2005"],
  "aliases": ["Möbius covariance of SLE", "force-weight balance", "chordal target change"],
  "prototypeUses": []
}
---

## Normalizing at the new target {#section-target-normalization}

<p>Let $g_t:\mathbb H\setminus K_t\to\mathbb H$ solve the chordal Loewner equation with a continuous real driver $U_t$:</p>
<div class="math-display">$$\partial_tg_t(z)=\frac2{g_t(z)-U_t},\qquad
g_t(z)=z+\frac{2t}{z}+O(z^{-2})\quad(z\to\infty).$$</div>
<p>Let $m$ be a real Möbius automorphism of $\mathbb H$, with $m(U_0)$ finite, and put $p=m^{-1}(\infty)$. Work before $p$ is swallowed. On each compact interval before that time, the image $m(K_t)$ is a bounded half-plane hull.</p>

<a id="tag-C6T0" data-assertion="proposition" data-title="A Möbius change of target has an explicit Loewner normalization and capacity clock"></a>
<p>There is a real Möbius map $\varphi_t$ such that the hydrodynamically normalized map for the image hull is</p>
<div class="math-display">$$\widehat g_{s(t)}=\varphi_t\circ g_t\circ m^{-1}.
\qquad s(t)=\int_0^t\varphi_r'(U_r)^2\,dr.$$</div>
<p>Its driver is $\widehat U_{s(t)}=\varphi_t(U_t)$. Writing $a_t=\varphi_t'(U_t)&gt;0$ and $b_t=\varphi_t''(U_t)$, one has</p>
<div class="math-display">$$\partial_t\varphi_t(z)=
\frac{2a_t^2}{\varphi_t(z)-\varphi_t(U_t)}
-\frac{2\varphi_t'(z)}{z-U_t},
\qquad (\partial_t\varphi_t)(U_t)=-3b_t.$$</div>
<p><em>Proof.</em> The affine case $m(z)=az+c$, $a&gt;0$, gives $\varphi_t=m$ and $s(t)=a^2t$ directly. Otherwise write</p>
<div class="math-display">$$m(z)=\alpha-\frac{\lambda}{z-p},\qquad \lambda&gt;0,
\qquad P_t=g_t(p),\quad Q_t=g_t'(p),\quad R_t=g_t''(p).$$</div>
<p>These boundary derivatives exist while $p$ is unswallowed, and $Q_t&gt;0$. The required map is</p>
<div class="math-display">$$\varphi_t(z)=c_t-\frac{d_t}{z-P_t},\qquad
c_t=\alpha-\frac{\lambda R_t}{2Q_t},\quad d_t=\lambda Q_t.$$</div>
<p>To check the normalization, use $m^{-1}(w)=p-\lambda/(w-\alpha)$ and expand $g_t$ at $p$. Then</p>
<div class="math-display">$$-\frac{\lambda Q_t}{g_t(m^{-1}(w))-P_t}
=w-\alpha+\frac{\lambda R_t}{2Q_t}+O(w^{-1}).$$</div>
<p>The constant $c_t$ cancels the remaining constant term. Thus $\varphi_t\circ g_t\circ m^{-1}$ is a conformal map onto $\mathbb H$ with expansion $w+O(w^{-1})$, so it is the hydrodynamically normalized map of $m(K_t)$.</p>
<p>Differentiating the Loewner equation at the unswallowed point gives, with $D_t=P_t-U_t$,</p>
<div class="math-display">$$P_t'=\frac2{D_t},\qquad
Q_t'=-\frac{2Q_t}{D_t^2},\qquad
R_t'=-\frac{2R_t}{D_t^2}+\frac{4Q_t^2}{D_t^3}.$$</div>
<p>Consequently $c_t'=-2d_t/D_t^3$ and $d_t'=-2d_t/D_t^2$. Substitution in the explicit rational map proves the displayed identity for $\partial_t\varphi_t(z)$. The apparent pole at $z=U_t$ cancels. Indeed, expanding $\varphi_t(U_t+h)=\varphi_t(U_t)+a_th+b_th^2/2+O(h^3)$ gives the value $-3b_t$ there.</p>
<p>For fixed $w$ outside the image hull, the two terms involving $g_t$ cancel in the chain rule, leaving</p>
<div class="math-display">$$\partial_t\bigl(\varphi_t(g_t(m^{-1}(w)))\bigr)
=\frac{2a_t^2}{\varphi_t(g_t(m^{-1}(w)))-\varphi_t(U_t)}.$$</div>
<p>Since $a_t&gt;0$, the clock $s$ is strictly increasing. Changing to this clock gives the chordal Loewner equation with driver $\widehat U$. Its coefficient of $w^{-1}$ grows at rate $2a_t^2$ and is initially zero, so the coefficient is $2s(t)$, as required. This also derives the capacity clock, rather than assuming its transformation rule. The formulas show that the coefficients of $\varphi_t$ are continuously differentiable in time on compact stops, even when $U$ is only continuous.</p>

## The balance of the force weights {#section-force-covariance}

<p>For boundary force points $V^1,\ldots,V^n$, use the convention that a point at $\infty$ stays there and contributes zero to the chordal drift. At finite marks the driving system is</p>
<div class="math-display">$$dU_t=\sqrt\kappa\,dB_t+
\sum_{j=1}^n\frac{\rho_j}{U_t-V_t^j}\,dt,
\qquad dV_t^j=\frac2{V_t^j-U_t}\,dt.$$</div>
<p>Stop before any force point collides with $U$, and before the new target $p=m^{-1}(\infty)$ is swallowed.</p>

<a id="tag-6RZ1" data-assertion="theorem" data-title="Chordal SLE with boundary forces is Möbius covariant when the weights sum to kappa minus six"></a>
<p>For $\kappa\geq0$, if $\sum_j\rho_j=\kappa-6$, then the image hulls, in the clock of C6T0, have the same force-point law started at $m(U_0),m(V_0^1),\ldots,m(V_0^n)$. More precisely, $\widehat V^j_{s(t)}=\varphi_t(V_t^j)$ and</p>
<div class="math-display">$$d\widehat U_s=\sqrt\kappa\,d\widehat B_s+
\sum_j\frac{\rho_j}{\widehat U_s-\widehat V_s^j}\,ds,
\qquad d\widehat V_s^j=\frac2{\widehat V_s^j-\widehat U_s}\,ds,$$</div>
<p>with the same convention at infinity. Without the sum condition, the transformed law has an additional force of weight $\kappa-6-\sum_j\rho_j$ at the image of the old target $\infty$. Forces already at that point are combined.</p>
<p><em>Proof.</em> For every real Möbius map $\varphi$ and admissible real $U,V$,</p>
<div class="math-display">$$\frac{\varphi'(U)}{U-V}
=\frac{\varphi'(U)^2}{\varphi(U)-\varphi(V)}
-\frac12\varphi''(U).$$</div>
<p>This follows immediately from $\varphi(z)=c-d/(z-P)$; the affine case has zero second derivative. Limits give the identity when $V=\infty$ or $\varphi(V)=\infty$.</p>
<p>The coefficients of $\varphi_t$ have finite variation by C6T0. Itô's formula therefore gives</p>
<div class="math-display">$$d\widehat U_{s(t)}=
a_t\sqrt\kappa\,dB_t+
\left(a_t\sum_j\frac{\rho_j}{U_t-V_t^j}
+\left(\frac\kappa2-3\right)b_t\right)dt.$$</div>
<p>Using the Möbius identity, its drift becomes</p>
<div class="math-display">$$a_t^2\sum_j\frac{\rho_j}{\widehat U_{s(t)}-\widehat V_{s(t)}^j}
+\frac{\kappa-6-\sum_j\rho_j}{2}\,b_t.$$</div>
<p>The last term vanishes under the stated balance. The process $\widehat B_s=\int_0^{t(s)}a_r\,dB_r$ has quadratic variation $s$, hence is Brownian motion in the new clock. For each finite force point, the chain rule and C6T0 similarly give</p>
<div class="math-display">$$d\varphi_t(V_t^j)=
\frac{2a_t^2}{\varphi_t(V_t^j)-\varphi_t(U_t)}\,dt.$$</div>
<p>The limiting forms of this calculation treat a point at infinity and a point mapped to infinity. Division by $ds/dt=a_t^2$ proves the transformed SDE. Local uniqueness identifies its law on compact stops; exhaustion gives the stated pre-collision result.</p>
<p>For arbitrary weights, append a force of weight $\kappa-6-\sum_j\rho_j$ at the original infinity. This changes no original chordal equation and restores the balance. Its image gives exactly the additional force claimed above. In particular, ordinary chordal SLE transforms with a force of weight $\kappa-6$ at the image of its old target. All these assertions retain the stopping restriction.</p>

## Bulk martingales in the new coordinates {#section-bulk-transfer}

<a id="tag-0INI" data-assertion="proposition" data-title="A bulk-covariant observable gives equivalent local martingales before and after a chordal target change"></a>
<p>Let $F(U,\mathbf V,w)$ be a real smooth function of admissible boundary marks and $w\in\mathbb H$, with only a bulk conformal weight $d\in\mathbb R$. Thus, for every real Möbius automorphism $m$ for which the marks are admissible,</p>
<div class="math-display">$$F(U,\mathbf V,w)=|m'(w)|^d
F(m(U),m(\mathbf V),m(w)).$$</div>
<p>For a pair of driving laws related by 6RZ1, and before swallowing $w$ or reaching any of the other stops, the process</p>
<div class="math-display">$$M_t=|g_t'(w)|^dF(U_t,\mathbf V_t,g_t(w))$$</div>
<p>is a local martingale if and only if its counterpart $\widehat M_s$ in the image coordinates is one. In fact, pathwise,</p>
<div class="math-display">$$M_t=|m'(w)|^d\,\widehat M_{s(t)}.$$</div>
<p><em>Proof.</em> Apply the covariance identity to the random Möbius map $\varphi_t$. Differentiating $\widehat g_{s(t)}\circ m=\varphi_t\circ g_t$ at $w$ gives</p>
<div class="math-display">$$\widehat g_{s(t)}'(m(w))\,m'(w)
=\varphi_t'(g_t(w))\,g_t'(w).$$</div>
<p>Taking absolute values and multiplying the covariance identity proves the pathwise formula. A positive time change and its inverse preserve local martingales after compact localization; the factor $|m'(w)|^d$ is deterministic. No expectation or terminal limit is taken.</p>
<p>For the strip candidate in <a href="/articles/continuum-connection-densities/#section-candidate-equation">the connection-density argument</a>, $d=5/48$ and the covariance follows directly from its defining strip map. The weights $(2,-2)$ at $\kappa=6$ satisfy 6RZ1. Sending the right force point to infinity therefore reduces the required local equation to the one-force calculation.</p>
