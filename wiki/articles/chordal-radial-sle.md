---
{
  "id": "chordal-radial-sle",
  "title": "Changing chordal and radial SLE targets",
  "subtitle": "Interior normalization, angular time and the force at the old target",
  "kind": "method",
  "category": "General theory",
  "summary": "Normalizing a chordal Loewner map at an interior point gives its radial clock explicitly. A rational vector-field identity then transports arbitrary mixtures of boundary and interior forces and identifies the compensating old-target force.",
  "context": [
    "The coordinate maps run between the upper half-plane and the unit disk, or from the disk to itself. Kappa may be zero; force weights are arbitrary real numbers.",
    "The proof uses the deterministic Loewner conformal-map theorem, uniqueness of normalized conformal maps, local SDE uniqueness, Itô calculus and Brownian time change.",
    "All transformations are stopped before a force collision or swallowing of the new target. No extension through that time or terminal trace statement is asserted."
  ],
  "related": ["sle-coordinate-changes", "radial-sle-martingales", "sle-force-martingales", "strip-sle"],
  "sourceIds": ["schramm-wilson-coordinate-changes-2005"],
  "aliases": ["chordal radial equivalence", "interior target normalization", "radial capacity clock"],
  "prototypeUses": []
}
---

## Normalizing at an interior point {#section-interior-normalization}

<p>Let $g_t:\mathbb H\setminus K_t\to\mathbb H$ solve $\partial_tg_t(z)=2/(g_t(z)-U_t)$ for a continuous real driver $U$. Fix a conformal bijection $\psi:\mathbb H\to\mathbb D$ and let $p=\psi^{-1}(0)$. Before $p$ is swallowed, put</p>
<div class="math-display">$$Z_t=x_t+iy_t=g_t(p),\quad Q_t=g_t'(p),\quad
c=(\psi^{-1})'(0),\quad
\lambda_t=i\frac{\overline{Q_tc}}{|Q_tc|},\quad
\varphi_t(z)=\lambda_t\frac{z-Z_t}{z-\overline Z_t}.$$</div>
<p>Here $y_t&gt;0$ and $Q_t\neq0$. The phase $\lambda_t$ has modulus one.</p>

<a id="tag-9BVE" data-assertion="proposition" data-title="Normalization at an interior target derives the radial Loewner equation and its positive clock"></a>
<p>The radial maps for the image hulls are</p>
<div class="math-display">$$\widehat g_{s(t)}=\varphi_t\circ g_t\circ\psi^{-1},\qquad
s(t)=\log\frac{|Q_tc|}{2y_t},\qquad
\widehat W_{s(t)}=\varphi_t(U_t).$$</div>
<p>They satisfy $s(0)=0$, $\widehat g_s(0)=0$, $\widehat g_s'(0)=e^s$ and</p>
<div class="math-display">$$s'(t)=h_t^2,\qquad
h_t=\frac{2y_t}{|U_t-Z_t|^2}
=\frac{\varphi_t'(U_t)}{i\varphi_t(U_t)}&gt;0,\qquad
\partial_s\widehat g_s(w)=-\widehat g_s(w)
\frac{\widehat g_s(w)+\widehat W_s}{\widehat g_s(w)-\widehat W_s}.$$</div>
<p><em>Proof.</em> The composite fixes zero, and its derivative there is $\lambda_tQ_tc/(2iy_t)=|Q_tc|/(2y_t)&gt;0$. At time zero it is a disk automorphism with these normalizations, hence the identity. In particular $s(0)=0$.</p>
<p>Write $D_t=(x_t-U_t)^2+y_t^2$. The chordal equation and its derivative give</p>
<div class="math-display">$$x_t'=\frac{2(x_t-U_t)}{D_t},\qquad
y_t'=-\frac{2y_t}{D_t},\qquad
\frac{Q_t'}{Q_t}=-\frac2{(Z_t-U_t)^2}.$$</div>
<p>Consequently</p>
<div class="math-display">$$s'(t)=\operatorname{Re}\frac{-2}{(Z_t-U_t)^2}+\frac2{D_t}
=\frac{4y_t^2}{D_t^2},\qquad
\frac{\lambda_t'}{\lambda_t}=\frac{4i(U_t-x_t)y_t}{D_t^2}.$$</div>
<p>The logarithmic derivative of $\varphi_t$ at the real point $U_t$ is $ih_t$. All coefficients of $\varphi_t$ are continuously differentiable in time, even when $U$ is merely continuous.</p>
<p>Use the radial vector field $\Psi(v,w)=-w(w+v)/(w-v)$. Substituting the preceding three derivatives into the rational map $\varphi_t$ gives</p>
<div class="math-display">$$\partial_t\varphi_t(z)+\frac{2\varphi_t'(z)}{z-U_t}
=h_t^2\Psi(\varphi_t(U_t),\varphi_t(z)).$$</div>
<p>This is an identity of rational functions: after taking out the common factor $\lambda_t$, it follows by multiplying by $(z-\overline Z_t)^2(z-U_t)D_t^2$. The chain rule now gives the radial equation for the composite. Its normalization was checked above, so it is the radial map of $\psi(K_t)$. On every compact stop before swallowing $p$, $h_t$ is positive and bounded above and below. The clock and its inverse are therefore well defined there.</p>

## Transporting interior and boundary forces {#section-mixed-force-change}

<p>For $\kappa\geq0$, the chordal force system is</p>
<div class="math-display">$$dU_t=\sqrt\kappa\,dB_t+
\sum_{j=1}^n\rho_j\operatorname{Re}\frac1{U_t-V_t^j}\,dt,\qquad
dV_t^j=\frac2{V_t^j-U_t}\,dt.$$</div>
<p>The initial marks may lie in $\overline{\mathbb H}$ or at infinity, but differ from the initial driver. An infinite mark stays at infinity and contributes zero to the driver. Stop before a force collision and before swallowing $p$. Coincident force marks can be combined.</p>
<p>For the disk, put $I(v)=1/\overline v$, with $I(0)=\infty$ and $I(\infty)=0$, and define $\widetilde\Psi(v,w)=(\Psi(v,w)+\Psi(I(v),w))/2$. At $|w|=1$, this symmetrized vector is tangent to the circle. In particular $\widetilde\Psi(0,w)=0$, using $\Psi(0,w)=-w$ and $\Psi(\infty,w)=w$.</p>

<a id="tag-5KL5" data-assertion="theorem" data-title="A chordal-to-radial map transports mixed force points and adds the compensating old-target force"></a>
<p>If $\sum_j\rho_j=\kappa-6$, the image hulls in the clock of 9BVE have radial force-point law with the same weights and marks $\widehat V_{s(t)}^j=\varphi_t(V_t^j)$:</p>
<div class="math-display">$$\begin{aligned}
d\widehat W_s&amp;=i\sqrt\kappa\,\widehat W_s\,d\widehat B_s
-\frac\kappa2\widehat W_s\,ds
+\sum_j\frac{\rho_j}{2}\widetilde\Psi(\widehat V_s^j,\widehat W_s)\,ds,\\
d\widehat V_s^j&amp;=\Psi(\widehat W_s,\widehat V_s^j)\,ds.
\end{aligned}$$</div>
<p>For arbitrary weights, the image law has in addition a force of weight $\Delta=\kappa-6-\sum_j\rho_j$ at the image of the old chordal target, $\lambda_t=\varphi_t(\infty)$. Existing weights at that point are combined. These conclusions include an original force at $p$, whose image is the radial target zero and has zero radial drift.</p>
<p><em>Proof.</em> Write $v^j=V^j$ and $v^{n+j}=\overline{V^j}$, assigning the same weight to both labels. Complex conjugation fixes a boundary or infinite mark, so this duplication also covers those cases. With $\Psi_{\mathbb H}(v,u)=2/(u-v)$, the chordal drift becomes $\sum_{j=1}^{2n}\rho_j\Psi_{\mathbb H}(v^j,U)/4$.</p>
<p>We use a local branch of $\log\widehat W$, or equivalently a continuous angular lift. Since the coefficients of $\varphi_t$ have finite variation, Itô's formula applies without a mixed quadratic-variation term. When $U$ has only its Brownian part, it gives</p>
<div class="math-display">$$d\log\widehat W_{s(t)}
=ih_t\sqrt\kappa\,dB_t
+\frac{\kappa-6}{2}h_t^2
\frac{\Psi(\lambda_t,\widehat W_{s(t)})}{\widehat W_{s(t)}}\,dt.$$</div>
<p>For instance, this follows by substituting the formulas of 9BVE into $\partial_t\log\varphi_t(U_t)+(\kappa/2)\partial_U^2\log\varphi_t(U_t)$. The first spatial derivative is $ih_t$, and the constant terms from the phase and moving target combine into the coefficient $\kappa-6$.</p>
<p>The force contribution is governed by a second rational identity, valid for a complex mark $v$:</p>
<div class="math-display">$$\frac{i}{h_t}\Psi_{\mathbb H}(v,U_t)
=\frac{\Psi(\varphi_t(v),\widehat W_{s(t)})}{\widehat W_{s(t)}}
-\frac{\Psi(\lambda_t,\widehat W_{s(t)})}{\widehat W_{s(t)}}.$$</div>
<p>It follows by substituting $\varphi_t(v)=\lambda_t(v-Z_t)/(v-\overline Z_t)$; limits give the identity at the exceptional points. Also $\varphi_t(\overline v)=I(\varphi_t(v))$. Multiplying by the duplicated weights and summing therefore gives</p>
<div class="math-display">$$\begin{aligned}
d\log\widehat W_{s(t)}={}&amp;ih_t\sqrt\kappa\,dB_t
+h_t^2\sum_{j=1}^n\frac{\rho_j}{2\widehat W_{s(t)}}
\widetilde\Psi(\widehat V_{s(t)}^j,\widehat W_{s(t)})\,dt\\
&amp;+\frac{\Delta}{2}h_t^2
\frac{\Psi(\lambda_t,\widehat W_{s(t)})}{\widehat W_{s(t)}}\,dt.
\end{aligned}$$</div>
<p>The process $\widehat B_s=\int_0^{t(s)}h_r\,dB_r$ has quadratic variation $s$, hence is Brownian motion up to the transformed stop. For $\Delta=0$, divide by the clock rate and exponentiate. The quadratic correction is $-\kappa\widehat W_s/2$, giving the claimed radial driver.</p>
<p>The mark equations follow from the vector-field identity in 9BVE. At $V=p$ the image is identically zero; at infinity it is $\lambda_t$, which satisfies the same radial boundary equation. Since $\lambda_t$ lies on the circle, its symmetrized force equals its ordinary force. The term with $\Delta$ is therefore exactly the additional old-target force. Local uniqueness identifies the laws, and exhaustion by compact stops retains precisely the pre-collision, pre-target scope. No assertion is made after a stop is reached.</p>

## Returning to the half-plane {#section-inverse-change}

<a id="tag-K4PV" data-assertion="theorem" data-title="A radial-to-chordal map adds the compensating force at the image of the radial target"></a>
<p>Let $f:\mathbb D\to\mathbb H$ be a conformal bijection with $f(W_0)$ finite. Radial SLE with mixed force weights $\rho_j$ maps, in half-plane capacity time, to chordal SLE with the same marks and weights and an additional force</p>
<div class="math-display">$$\kappa-6-\sum_j\rho_j\quad\text{at }f(0).$$</div>
<p>The laws are identified on compact stops before force collisions or swallowing $f^{-1}(\infty)$. A force already at zero is combined with the added weight after mapping. In particular, ordinary radial SLE becomes chordal SLE with weight $\kappa-6$ at the image of its interior target. Conversely, ordinary chordal SLE becomes radial SLE with weight $\kappa-6$ at the image of its boundary target.</p>
<p><em>Proof.</em> Start a chordal process with the image marks and the additional weight $\Delta=\kappa-6-\sum_j\rho_j$ at $f(0)$. Its total weight is $\kappa-6$. Apply 5KL5 with $\psi=f^{-1}$. The resulting radial process has the prescribed original forces and a force of weight $\Delta$ at zero. The latter has zero symmetrized radial drift, so local uniqueness gives the desired radial law.</p>
<p>This identifies the inverse transformation as well. A conformal image determines its hull, and the hydrodynamic normalization determines both the half-plane map and its capacity parameter uniquely. Thus mapping the coupled radial hulls back by $f$ recovers the chordal process and the inverse of the strictly increasing clock. Before $f^{-1}(\infty)$ is swallowed, image hulls on compact stops are bounded half-plane hulls. Their normalizations vary continuously, and the clock rate is positive and bounded away from zero locally. Repeating the local identification and exhausting these stops gives the stated inverse law. The boundary-target stop is essential; it is not removed by the inversion argument.</p>
<p>The ordinary radial case has no original weights, so $\Delta=\kappa-6$. The ordinary chordal case is the arbitrary-weight conclusion of 5KL5 with an empty original list. At $\kappa=6$ both compensating weights vanish, still with the same stopping restrictions.</p>

## The derivative in the clock formula {#section-clock-convention}

<p>The positive clock in 9BVE can be written in either of the equivalent forms</p>
<div class="math-display">$$s'(t)=|\varphi_t'(U_t)|^2
=\left(\frac{\varphi_t'(U_t)}{i\varphi_t(U_t)}\right)^2.$$</div>
<p>The second expression squares the angular boundary derivative. It does not square the complex derivative without a modulus. For example, take $\psi(z)=(z-i)/(z+i)$ and $U_0=0$. Then $\varphi_0(0)=-1$, $\varphi_0'(0)=-2i$ and $s'(0)=4$, whereas $\varphi_0'(0)^2=-4$.</p>
<p><a href="https://arxiv.org/html/math/0505368v3">Schramm–Wilson, Remark 4</a> writes the clock as $\varphi_t'(U_t)^2$. With $\varphi_t$ understood as the complex Möbius map in the preceding proof, this needs a modulus; alternatively, the prime in that particular formula must explicitly mean the angular derivative. The earlier explicit calculation of the clock in Theorem 3 is already correct. This convention issue is recorded <a href="/errata/schramm-wilson-coordinate-changes-2005/#radial-clock-derivative">provisionally</a>; it does not alter the theorem or its force-weight balance.</p>

## Moving the target within the disk {#section-disk-normalization}

<p>Let $g_t$ now be a radial Loewner chain with continuous driver $W_t\in\partial\mathbb D$, and let $f$ be an automorphism of $\mathbb D$. Put $p=f^{-1}(0)$ and $c=(f^{-1})'(0)$. Before $p$ is swallowed, define</p>
<div class="math-display">$$Z_t=g_t(p),\quad Q_t=g_t'(p),\quad
\lambda_t=\frac{\overline{Q_tc}}{|Q_tc|},\quad
\varphi_t(z)=\lambda_t\frac{z-Z_t}{1-\overline Z_tz},\quad
F_t=\varphi_t\circ g_t\circ f^{-1}.$$</div>

<a id="tag-JVHZ" data-assertion="proposition" data-title="Direct disk normalization gives the radial clock without an intermediate boundary target"></a>
<p>The image hulls have normalized radial maps $\widehat g_{s(t)}=F_t$ and driver $\widehat W_{s(t)}=\varphi_t(W_t)$, where</p>
<div class="math-display">$$s(t)=\log\frac{|Q_tc|}{1-|Z_t|^2},\qquad
s'(t)=h_t^2,\qquad
h_t=\frac{1-|Z_t|^2}{|W_t-Z_t|^2}
=\frac{W_t\varphi_t'(W_t)}{\varphi_t(W_t)}>0.$$</div>
<p>This construction requires only that the new interior target remain unswallowed.</p>
<p><em>Proof.</em> The composite fixes zero and has positive derivative $|Q_tc|/(1-|Z_t|^2)$ there. Thus $F_0$ is the identity. Write $A_t=\partial_z\Psi(W_t,Z_t)$. Differentiating the original Loewner equation gives</p>
<div class="math-display">$$Z_t'=\Psi(W_t,Z_t),\qquad Q_t'/Q_t=A_t,\qquad
\lambda_t'/\lambda_t=-i\operatorname{Im}A_t.$$</div>
<p>Consequently</p>
<div class="math-display">$$s'(t)=\operatorname{Re}A_t+
\frac{2\operatorname{Re}\bigl(\overline Z_t\Psi(W_t,Z_t)\bigr)}
 {1-|Z_t|^2}=h_t^2.$$</div>
<p>Substitution into the disk automorphism also gives</p>
<div class="math-display">$$\partial_t\varphi_t(z)+\varphi_t'(z)\Psi(W_t,z)
=h_t^2\Psi(\varphi_t(W_t),\varphi_t(z)).$$</div>
<p>For these rational identities one may rotate $W_t$ to $1$ and factor out $\lambda_t$; inserting $\Psi(1,z)=z(1+z)/(1-z)$ reduces them to equalities with denominators that are nonzero before swallowing. The chain rule proves the radial equation for $F_t$. Its normalization identifies the image chain. On compact stops, $|Z_t|$ stays below one and $h_t$ is bounded above and away from zero. No intermediate boundary point enters the construction.</p>

## Radial forces under a disk automorphism {#section-disk-forces}

<a id="tag-V2NR" data-assertion="theorem" data-title="A disk automorphism transports mixed radial forces with a compensating old-target force"></a>
<p>For $\kappa\geq0$, let a radial force-point process have initial marks in $\overline{\mathbb D}\setminus\{W_0\}$ and real weights $\rho_j$. Under the automorphism $f$ and clock of JVHZ, its image has the same weights at the image marks and an additional force of weight</p>
<div class="math-display">$$\Delta=\kappa-6-\sum_j\rho_j$$</div>
<p>at $f(0)$, the image of the old radial target. The law is identified up to force collisions or swallowing $f^{-1}(0)$, by exhaustion of compact stops. Coincident weights are combined; a force at the current target has zero drift. In particular, when the weights sum to $\kappa-6$ there is no added force, and ordinary radial SLE has target-change weight $\kappa-6$.</p>
<p><em>Proof.</em> Set $a_t=\varphi_t(0)$ and $\widehat V_{s(t)}^j=\varphi_t(V_t^j)$. The vector-field identity in JVHZ gives the radial evolution of every image mark, including $a_t$. We need only identify the driver.</p>
<p>For $W=e^{i\theta}$, the angular derivative is $\partial_\theta\log\varphi_t(W)=ih_t$. Applying the derivatives in JVHZ to a local logarithm gives the unforced identity</p>
<div class="math-display">$$\left(\partial_t+\frac\kappa2\partial_\theta^2\right)
\log\varphi_t(e^{i\theta})\bigg|_{e^{i\theta}=W_t}
=\frac{\kappa-6}{2}h_t^2
\frac{\widetilde\Psi(a_t,\widehat W_{s(t)})}{\widehat W_{s(t)}}.$$</div>
<p>The force contribution follows from</p>
<div class="math-display">$$h_t\frac{\widetilde\Psi(v,W_t)}{W_t}
=h_t^2\left(
\frac{\widetilde\Psi(\varphi_t(v),\widehat W_{s(t)})}{\widehat W_{s(t)}}
-\frac{\widetilde\Psi(a_t,\widehat W_{s(t)})}{\widehat W_{s(t)}}
\right).$$</div>
<p>Both are rational identities. To check the first, use $\partial_\theta=iW\partial_W$ with the coefficients of $\varphi_t$ held fixed in the spatial derivatives, and $\lambda_t'/\lambda_t=-i\operatorname{Im}A_t$ in the time derivative. For the second, pair $v$ with $1/\overline v$ and use $\varphi_t(1/\overline v)=1/\overline{\varphi_t(v)}$. Rotation reduces both checks to $W=1$ and $\lambda=1$. Limits include $v=0$, where the left side is zero and the two terms on the right coincide.</p>
<p>The coefficients of $\varphi_t$ have finite variation, so there is no mixed quadratic-variation term. The preceding identities give</p>
<div class="math-display">$$\begin{aligned}
d\log\widehat W_{s(t)}={}&ih_t\sqrt\kappa\,dB_t\\
&+h_t^2\left(
\sum_j\frac{\rho_j}{2}
\frac{\widetilde\Psi(\widehat V_{s(t)}^j,\widehat W_{s(t)})}{\widehat W_{s(t)}}
+\frac{\Delta}{2}
\frac{\widetilde\Psi(a_t,\widehat W_{s(t)})}{\widehat W_{s(t)}}
\right)dt.
\end{aligned}$$</div>
<p>Changing time with $ds=h_t^2dt$ makes $\int h_t\,dB_t$ Brownian, and exponentiating supplies the usual drift $-\kappa\widehat W_s/2$. This is precisely the radial force system with the additional weight $\Delta$ at $a$. Local uniqueness and exhaustion by compact stops prove the claim on the stated lifetime. In particular, the disk-to-disk case of the coordinate theorem needs no stop at an auxiliary boundary target.</p>

