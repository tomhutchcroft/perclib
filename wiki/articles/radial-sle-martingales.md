---
{
  "id": "radial-sle-martingales",
  "title": "Radial SLE force-point martingales",
  "subtitle": "Reflection, boundary limits and the weights suggested by rare events",
  "kind": "method",
  "category": "General theory",
  "summary": "Reflection in the unit circle turns the radial force-point product into a symmetric expression. Its logarithmic drift is a quadratic form, giving a local martingale and a stopped change of measure. Boundary limits yield the percolation and spanning-tree candidate weights.",
  "context": [
    "The radial target is the origin, the disk maps have derivative exp(t) there, and kappa is positive.",
    "The argument uses deterministic radial Loewner maps, Schwarz reflection, Itô calculus, Novikov's criterion, Girsanov's theorem and local SDE uniqueness.",
    "The results are local or stopped. The paper's proposed interpretations as discrete rare-event probabilities require additional scaling-limit and terminal arguments."
  ],
  "related": ["sle-force-martingales", "sle-coordinate-changes", "sle-conformal-radius", "strip-sle"],
  "sourceIds": ["schramm-wilson-coordinate-changes-2005"],
  "aliases": ["radial force-point density", "reflected SLE martingale", "pivotal and spanning-tree candidate weights"],
  "prototypeUses": []
}
---

## A product over reflected marks {#section-reflected-product}

<p>Let $\kappa&gt;0$, $\Theta_t=\theta+\sqrt\kappa B_t$ and $W_t=e^{i\Theta_t}$. The ordinary radial Loewner maps satisfy</p>
<div class="math-display">$$\partial_tg_t(z)=g_t(z)\frac{W_t+g_t(z)}{W_t-g_t(z)},\qquad
g_0(z)=z,\quad g_t(0)=0,\quad g_t'(0)=e^t.$$</div>
<p>Choose distinct nonzero marks $z_1,\ldots,z_n$ in the open disk and real weights $\rho_1,\ldots,\rho_n$. Add reflected marks $z_{n+j}=1/\overline z_j$ with weights $\rho_{n+j}=\rho_j$. Extend the maps by $g_t(1/\overline z)=1/\overline{g_t(z)}$, wherever the original map is defined. Write $Z_j=g_t(z_j)$ and $J_j=|g_t'(z_j)|$ for all $2n$ labels. All assertions below are made before any original mark is swallowed.</p>

<a id="tag-T723" data-assertion="theorem" data-title="The reflected radial force-point product is a positive local martingale"></a>
<p>Put $S=\sum_{j=1}^n\rho_j$ and</p>
<div class="math-display">$$q_0=\frac{(4+S)S}{8\kappa},\qquad
q_j=\frac{(8-2\kappa+\rho_j)\rho_j}{16\kappa},\qquad
M_t=e^{q_0t}\prod_{j=1}^{2n}|W_t-Z_j|^{\rho_j/(2\kappa)}J_j^{q_j}
\prod_{i&lt;j}|Z_i-Z_j|^{\rho_i\rho_j/(8\kappa)}.$$</div>
<p>Define $R_j=(W_t+Z_j)/(W_t-Z_j)$ and $H_t=\sum_{j=1}^n\rho_j\operatorname{Im}R_j$. Then</p>
<div class="math-display">$$\frac{dM_t}{M_t}=-\frac{H_t}{2\sqrt\kappa}\,dB_t,\qquad
\frac{M_t}{M_0}=\exp\left(-\int_0^t\frac{H_r}{2\sqrt\kappa}\,dB_r
-\frac1{8\kappa}\int_0^tH_r^2\,dr\right).$$</div>
<p>In particular $M$ is a positive local martingale.</p>
<p><em>Proof.</em> Reflection gives $R_{n+j}=-\overline R_j$. This is the cancellation that determines the radial factor $e^{q_0t}$. To see it in the product, the needed logarithmic differentials are</p>
<div class="math-display">$$\begin{aligned}
d\log|W_t-Z_j|&amp;=-\frac{\sqrt\kappa}{2}\operatorname{Im}R_j\,dB_t
+\operatorname{Re}\left(\frac{\kappa-4}{8}R_j^2+\frac{R_j}{2}-\frac\kappa8\right)dt,\\
d\log J_j&amp;=\frac12\operatorname{Re}(R_j^2+2R_j-1)\,dt,\\
d\log|Z_i-Z_j|&amp;=\frac12\operatorname{Re}(R_iR_j+R_i+R_j-1)\,dt.
\end{aligned}$$</div>
<p>The first identity follows from $dW=i\sqrt\kappa W\,dB-\kappa W\,dt/2$ and $dZ_j=Z_jR_j\,dt$. For the other two, with $W$ fixed, the vector field $v(z)=z(W+z)/(W-z)$ satisfies</p>
<div class="math-display">$$v'(z)=\frac{R(z)^2+2R(z)-1}{2},\qquad
\frac{v(z)-v(w)}{z-w}=\frac{R(z)R(w)+R(z)+R(w)-1}{2}.$$</div>
<p>Set $S_0=\sum_{j=1}^{2n}\rho_j=2S$ and $S_1=\sum_{j=1}^{2n}\rho_jR_j=2iH_t$. Substituting the three differentials into $\log M$, the quadratic, linear and constant terms collect as</p>
<div class="math-display">$$\operatorname{drift}(d\log M_t)
=q_0+\frac1{32\kappa}\operatorname{Re}\left(
S_1^2+(24-4\kappa+2S_0)S_1-8S_0-S_0^2\right).
$$</div>
<p>For completeness, the quadratic terms are $\sum_j\rho_j^2R_j^2+2\sum_{i&lt;j}\rho_i\rho_jR_iR_j=S_1^2$. The linear terms have coefficient $24-4\kappa+2S_0$, and the constant terms are $-8S_0-S_0^2$. The choice of $q_0$ cancels these constants. Since $S_1$ is purely imaginary, the remaining drift is $-H_t^2/(8\kappa)$. The Brownian coefficient is $-\operatorname{Im}S_1/(4\sqrt\kappa)=-H_t/(2\sqrt\kappa)$. Exponentiating proves the formula. Compact localization keeps every denominator and derivative admissible, and exhaustion gives the local result.</p>
<p>A force mark at the radial target can be omitted: $R(0)=1$ contributes no angular drift. This also agrees with the normalized product limit as a mark of weight $r$ tends to zero. Indeed $g_t(z)\sim e^tz$, its reflected image is asymptotic to $e^{-t}/\overline z$, and the product of the two derivative factors tends to one. The new gap, reflected-pair and interaction factors contribute respectively $e^{-rt/(2\kappa)}$, $e^{-r^2t/(8\kappa)}$ and $e^{-rSt/(4\kappa)}$ after initial normalization. The change in $q_0$ is $(4r+r^2+2rS)/(8\kappa)$, so these factors cancel. The normalized limit is the product with the center mark removed.</p>

## Marks on the boundary {#section-boundary-limit}

<p>Let some of the original marks lie on the unit circle, still distinct from each other and from $W_0$. Reflection now duplicates these labels at the same point. Before swallowing a boundary mark, the map extends analytically across it, and $J_j$ is its positive angular derivative.</p>

<a id="tag-EU7X" data-assertion="proposition" data-title="Boundary renormalization extends the radial product to mixed interior and boundary marks"></a>
<p>In the doubled product of T723, replace the vanishing factor for each original boundary mark by</p>
<div class="math-display">$$|Z_j-Z_{n+j}|^{\rho_j^2/(8\kappa)}
\quad\longmapsto\quad J_j^{\rho_j^2/(8\kappa)}.$$</div>
<p>Keep every other pair factor, including its multiplicity, and identify the two reflected copies elsewhere. The resulting positive product satisfies the same stochastic-exponential identity as T723, with $H_t$ summed over the original marks. In particular, when all marks lie on the boundary, it is</p>
<div class="math-display">$$M_t=e^{q_0t}
\prod_{j=1}^nJ_j^{h_j}|W_t-Z_j|^{\rho_j/\kappa}
\prod_{i&lt;j\leq n}|Z_i-Z_j|^{\rho_i\rho_j/(2\kappa)},
\qquad h_j=\frac{\rho_j(\rho_j+4-\kappa)}{4\kappa}.$$</div>
<p><em>Proof.</em> Approach a boundary mark $\zeta$ from inside along $r\zeta$, with reflected mark $r^{-1}\zeta$. Analytic continuation gives, uniformly on compact stops before swallowing $\zeta$,</p>
<div class="math-display">$$\frac{|g_t(r\zeta)-g_t(r^{-1}\zeta)|}
{|r\zeta-r^{-1}\zeta|}\longrightarrow |g_t'(\zeta)|.$$</div>
<p>The initial denominator disappears in $M_t/M_0$. Every other factor has a finite nonzero limit, yielding exactly the stated replacement. On a further compact stop, the stochastic-logarithm integrands in T723 converge uniformly and are bounded. Their stochastic integrals converge in $L^2$ on bounded time intervals, and their squared-integrand time integrals converge as well. Passing to the exponential identity therefore proves the asserted identity for the limit; this does not rely on an unstopped limit of local martingales.</p>
<p>For the all-boundary formula, the two derivative powers and the replaced diagonal power sum to $2q_j+\rho_j^2/(8\kappa)=h_j$. The two driver gaps give exponent $\rho_j/\kappa$, and the four pairs between two different original marks give exponent $\rho_i\rho_j/(2\kappa)$. The same limiting argument treats several boundary marks at once since they remain separated on the chosen stop.</p>

## The radial force law {#section-radial-weighting}

<a id="tag-MLBQ" data-assertion="proposition" data-title="The radial product produces the radial force-point law on compact stops"></a>
<p>For the interior or mixed product above, let $\sigma$ keep the configuration in a compact part of its pre-swallowing state space, and let $T&lt;\infty$. The density $M_{T\wedge\sigma}/M_0$ defines a probability measure under which, before $T\wedge\sigma$,</p>
<div class="math-display">$$d\Theta_t=\sqrt\kappa\,d\widetilde B_t
-\frac12\sum_{j=1}^n\rho_j\operatorname{Im}\frac{W_t+Z_j}{W_t-Z_j}\,dt,
\qquad dZ_j=Z_j\frac{W_t+Z_j}{W_t-Z_j}\,dt.$$</div>
<p>This is the radial force-point law, with no restriction on the sum of the weights.</p>
<p><em>Proof.</em> On the stop, $H_t$ is bounded, so Novikov's criterion makes the normalized exponential a true martingale. Girsanov changes the Brownian increment in $d\Theta$ by $-H_t\,dt/(2\sqrt\kappa)$, giving the displayed drift. The mark equations hold pathwise and are unchanged. Local uniqueness identifies the stopped law.</p>
<p>To compare with the reflected-vector-field convention, write $\Psi(v,w)=-w(w+v)/(w-v)$. For $|W|=1$,</p>
<div class="math-display">$$\frac{\Psi(Z,W)+\Psi(1/\overline Z,W)}2
=-iW\operatorname{Im}\frac{W+Z}{W-Z}.$$</div>
<p>Thus Itô's formula for $W=e^{i\Theta}$ gives precisely the symmetrized force term, together with $-\kappa W/2$ from the Brownian motion on the circle. For boundary marks $Z_j=e^{i\Phi_j}$, the angular equations reduce to</p>
<div class="math-display">$$d\Theta_t=\sqrt\kappa\,d\widetilde B_t+
\frac12\sum_j\rho_j\cot\frac{\Theta_t-\Phi_j}{2}\,dt,
\qquad d\Phi_j=\cot\frac{\Phi_j-\Theta_t}{2}\,dt.$$</div>
<p>The positive density gives equivalence on each stopped interval. It gives neither a density at the swallowing time nor an identification with conditioning on a discrete event.</p>

## The weights for several approaching curves {#section-rare-event-weights}

<a id="tag-O8ZR" data-assertion="corollary" data-title="Equal boundary weights give the radial percolation and spanning-tree candidate martingales"></a>
<p>Take $N-1$ distinct boundary force marks of weight $2$, let $Z_N=W_t$, and assume $N\geq2$. Up to the first collision,</p>
<div class="math-display">$$M_t=
e^{(N^2-1)t/(2\kappa)}
\prod_{j=1}^{N-1}J_j^{(6-\kappa)/(2\kappa)}
\prod_{1\leq i&lt;j\leq N}|Z_i-Z_j|^{2/\kappa}$$</div>
<p>is a positive local martingale. Consequently the two special cases are</p>
<div class="math-display">$$\begin{aligned}
\kappa=6:\quad &amp;M_t=e^{(N^2-1)t/12}\prod_{i&lt;j}|Z_i-Z_j|^{1/3},\\
\kappa=2:\quad &amp;M_t=e^{(N^2-1)t/4}\prod_{j&lt;N}J_j\prod_{i&lt;j}|Z_i-Z_j|.
\end{aligned}$$</div>
<p><em>Proof.</em> Substitute $S=2(N-1)$ and $\rho_j=2$ into EU7X. The radial exponent is $(N^2-1)/(2\kappa)$, the derivative exponent is $(6-\kappa)/(2\kappa)$, and both sorts of gap have exponent $2/\kappa$. This combines the driver gaps and mark pairs into the one product displayed above.</p>
<p>These identities explain the weights discussed in <a href="https://arxiv.org/html/math/0505368v3">Schramm–Wilson, Remark 8</a>. At $\kappa=6$ the boundary derivatives disappear; with four marked points the radial exponent is $5/4$. At $\kappa=2$ each retained boundary derivative has power one; with three marked points the radial exponent is $2$. Also $\operatorname{crad}_{\mathbb D\setminus K_t}(0)=e^{-t}$, so the exponential factors are powers of inverse conformal radius.</p>
<p>The source proposes using these weights for a pivotal percolation site and for several branches of a wired uniform spanning tree approaching an interior point. Its formulas (10)–(11) additionally include microscopic scales, boundary densities in the tree case, and an asymptotic constant. O8ZR establishes the local martingale algebra. Identifying any such expression with a discrete rare-event probability still requires a scaling limit, the appropriate terminal event and an argument controlling expectations at that terminal time. For more than six percolation arms the source also distinguishes approaching a site from distinct interfaces literally meeting its hexagon. None of these probability identifications is used as a proved input here.</p>
