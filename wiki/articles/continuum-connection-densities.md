---
{
  "id": "continuum-connection-densities",
  "title": "Continuum connection densities",
  "subtitle": "The angular spectrum and the boundary conditioning law",
  "kind": "method",
  "category": "General theory",
  "summary": "The angular diffusion has an explicit Jacobi spectrum. Its leading coefficient gives the bulk connection density, while Cardy's boundary density determines the stopped SLE change of measure and the correct joint differential operator.",
  "context": [
    "The analytic spectral calculation is proved below. Identifying the angular semigroup with critical triangular-site percolation is a separate radial-SLE input.",
    "Cardy's formula, conformal invariance, the SLE domain Markov property and standard Itô/Girsanov calculus are explicit inputs to the probabilistic applications.",
    "All SLE changes of measure are stopped away from collisions. No terminal conditioning or five-point optional-stopping argument is inferred from a local martingale alone."
  ],
  "related": ["planar-factorization", "adaptive-three-point", "critical-exponents"],
  "sourceIds": ["beliaev-izyurov-factorization-2012", "conijn-factorization-2015"],
  "aliases": ["Jacobi spectrum", "one-arm constant", "Cardy density", "SLE force points"],
  "prototypeUses": []
}
---

## The angular operator {#section-angular-operator}

<p>The radial calculation in Beliaev–Izyurov starts with the operator</p>
<div class="math-display">$$L_\theta=3\partial_\theta^2+\cot(\theta/2)\partial_\theta,\qquad 0&lt;\theta&lt;2\pi.$$</div>
<p>It has a killing boundary at $0$ and a reflecting boundary at $2\pi$. These boundary choices matter: the differential expression alone does not determine an operator. The substitution $y=\sin^2(\theta/4)$ makes them particularly transparent.</p>

<a id="tag-O3HO" data-assertion="definition" data-title="The mixed-boundary angular semigroup is defined by its weighted energy form"></a>
<p>On $(0,1)$ put</p>
<div class="math-display">$$\rho(y)=y^{-1/6}(1-y)^{-1/6},\qquad p(y)=\tfrac34y^{5/6}(1-y)^{5/6},\qquad \mathcal E(f,g)=\int_0^1p f'g'\,dy.$$</div>
<p>The form domain consists of locally absolutely continuous functions with $\int_0^1(f^2\rho+p(f')^2)\,dy&lt;\infty$ and trace $f(0)=0$; there is no constraint on $f(1)$. The nonpositive self-adjoint operator $A$ associated with this closed form satisfies $\mathcal E(f,g)=\langle-Af,g\rangle_{L^2(\rho)}$. Write $T_s=e^{sA}$.</p>
<p>Both traces exist, since $\int_0^1p^{-1}&lt;\infty$ and weighted Cauchy–Schwarz controls $|f(v)-f(u)|$. The same estimate makes the zero-trace constraint closed. Completeness follows by taking the local weak derivative of a Cauchy sequence in the form norm. Smooth functions of compact support are dense in $L^2(\rho)$, so the closed-form representation theorem applies. This standard Hilbert-space theorem is the functional-analytic input used here.</p>
<p>Integration by parts gives</p>
<div class="math-display">$$Af=\rho^{-1}(pf')'=\tfrac34y(1-y)f''+\tfrac58(1-2y)f'.$$</div>
<p>Its boundary condition at $1$ is zero flux, $\lim_{y\uparrow1}p(y)f'(y)=0$. At $0$ the test functions vanish and a nonzero flux is allowed. The chain rule identifies this expression with $L_\theta$. In the original angle variable the form has weight proportional to $\sin^{2/3}(\theta/2)$; the reflecting condition is the natural weighted one, not an additional absorbing endpoint.</p>

## The complete spectrum {#section-jacobi-spectrum}

<a id="tag-8X8I" data-assertion="theorem" data-title="A ground-state change reduces the angular spectrum to Jacobi polynomials"></a>
<p>Let $h_0(y)=y^{1/6}$, $\lambda_0=5/48$, and let $P_n$ be the degree-$n$ orthonormal polynomials for the probability measure</p>
<div class="math-display">$$\pi(dy)=\frac{y^{1/6}(1-y)^{-1/6}}{B(7/6,5/6)}\,dy,\qquad P_0=1.$$</div>
<p>Then $h_0P_n$ form a complete orthogonal eigenbasis for $A$, with eigenvalues</p>
<div class="math-display">$$-\frac{5}{48}-\frac34n(n+1),\qquad n=0,1,2,\ldots.$$</div>
<p><em>Proof.</em> Direct differentiation gives $Ah_0=-\lambda_0h_0$ and</p>
<div class="math-display">$$h_0^{-1}(A+\lambda_0)(h_0g)=\mathcal Jg
=\tfrac34y(1-y)g''+\left(\tfrac78-\tfrac32y\right)g'.$$</div>
<p>The operator $\mathcal J$ is symmetric for $\pi$. For polynomials $f,g$, integration by parts has no boundary term because the flux weight is proportional to $y^{7/6}(1-y)^{5/6}$, and gives $\langle f,\mathcal Jg\rangle_\pi=-\tfrac34\int y(1-y)f'g'\,d\pi$. It preserves polynomial degree, and its coefficient on $y^n$ is $-\tfrac34n(n+1)$. For each lower-degree polynomial $q$, symmetry gives $\langle\mathcal JP_n,q\rangle=\langle P_n,\mathcal Jq\rangle=0$. Hence $\mathcal JP_n=-\tfrac34n(n+1)P_n$.</p>
<p>Each $h_0P_n$ belongs to the form domain. Near zero its derivative has order $y^{-5/6}$, so its energy is bounded by a constant times $\int_0^{1/2}y^{-5/6}\,dy$. Its flux vanishes at $1$. Integration by parts against the form domain therefore puts it in the operator domain, with the claimed eigenvalue. Polynomials are dense in $L^2(\pi)$: continuous functions are dense for this finite measure and are uniformly approximated by polynomials. Multiplication by $h_0$ identifies this space, up to a constant normalization, with $L^2(\rho)$. Thus the eigenfunctions are complete. The self-adjoint operator is diagonal in this basis, proving the entire spectrum and the spectral gap $3/2$ above the leading decay rate.</p>
<p>In the source's unweighted representation $f=\sin^{1/3}(\theta/2)h$, the operator is $3\Lambda$, where $\Lambda=\partial_\theta^2+1/12+(1/18)\cot^2(\theta/2)$. Its eigenfunctions are</p>
<div class="math-display">$$\bigl(\sin(\theta/2)\sin(\theta/4)\bigr)^{1/3}P_n\bigl(\sin^2(\theta/4)\bigr),$$</div>
<p>and the eigenvalues of $\Lambda$ are $-5/144-n(n+1)/4$. Evolution uses three times these eigenvalues.</p>

## The one-arm coefficient {#section-uniform-asymptotic}

<a id="tag-DCSM" data-assertion="theorem" data-title="The mixed-boundary survival function has a uniform relative asymptotic with coefficient eighteen over five pi"></a>
<p>Set $h(\theta,s)=(T_s1)(\sin^2(\theta/4))$. There is a constant $C&lt;\infty$ such that, for $s\geq1$,</p>
<div class="math-display">$$\sup_{0&lt;\theta\leq2\pi}\left|
\frac{e^{5s/48}h(\theta,s)}{\sin^{1/3}(\theta/4)}-\frac{18}{5\pi}\right|
\leq Ce^{-3s/2}.$$</div>
<p><em>Proof.</em> The initial function in the transformed space is $g_0=h_0^{-1}=y^{-1/6}$, which belongs to $L^2(\pi)$. Write $a_n=\langle g_0,P_n\rangle_\pi$. The spectral expansion gives</p>
<div class="math-display">$$e^{5s/48}\frac{(T_s1)(y)}{h_0(y)}
=\sum_{n\geq0}a_ne^{-3n(n+1)s/4}P_n(y).$$</div>
<p>The constant coefficient is</p>
<div class="math-display">$$a_0=\frac{B(1,5/6)}{B(7/6,5/6)}
=\frac{6/5}{\Gamma(7/6)\Gamma(5/6)}=\frac{18}{5\pi},$$</div>
<p>where the last equality uses the gamma recurrence and reflection formulas.</p>
<p>To justify uniform convergence, it is enough to bound the normalized polynomials by a power of their degree. If $M=\|P_n\|_\infty$, Markov's polynomial inequality on $[0,1]$ gives $\|P_n'\|_\infty\leq2n^2M$. Around a point where $|P_n|=M$, there is a one-sided interval of length $1/(4n^2)$ on which $|P_n|\geq M/2$. Every interval of length $\delta$ has $\pi$-mass at least $c\delta^{7/6}$, since its density is at least a constant times $y^{1/6}$. Normalization now gives $\|P_n\|_\infty\leq C_0(n+1)^{7/6}$. The assertion for $n=0$ is immediate.</p>
<p>By Cauchy–Schwarz and Parseval, the nonconstant part of the expansion is bounded uniformly in $y$ by</p>
<div class="math-display">$$\|g_0\|_{L^2(\pi)}C_0
\left(\sum_{n\geq1}(n+1)^{7/3}e^{-3n(n+1)s/2}\right)^{1/2}
\leq C e^{-3s/2},\qquad s\geq1.$$</div>
<p>This also provides a continuous representative up to both endpoints. At $y=0$ the original function vanishes; the ratio in the theorem refers to its continuous extension from positive $y$. No pointwise convergence is deduced merely from an $L^2$ limit.</p>

<a id="tag-Q4NI" data-assertion="corollary" data-title="The radial-SLE identification gives the bulk-boundary density with its exact coefficient"></a>
<p>Assume the radial-SLE identification used in Beliaev–Izyurov Lemma 2.2: the probability that the cluster attached to an arc of angular length $\theta$ in the unit disk comes within conformal radius $e^{-s}$ of zero is $h(\theta,s)$ for the mixed-boundary semigroup above. Let $D$ be simply connected, $w\in D$, and let a boundary arc have harmonic measure $\omega\in(0,1]$ from $w$. If $\phi:D\to\mathbb D$ sends $w$ to zero, then</p>
<div class="math-display">$$\mathbb P\bigl(r(w)&lt;\varepsilon\bigr)
=\frac{18}{5\pi}\varepsilon^{5/48}|\phi'(w)|^{5/48}
\sin^{1/3}(\pi\omega/2)
\left(1+O\bigl((\varepsilon|\phi'(w)|)^{3/2}\bigr)\right).$$</div>
<p>The error is uniform in the arc when $\varepsilon|\phi'(w)|\leq e^{-1}$. <em>Proof.</em> Conformal radius scales by $|\phi'(w)|$, while the image arc has length $2\pi\omega$. Apply DCSM with $s=-\log(\varepsilon|\phi'(w)|)$ and divide its absolute error by the positive constant $18/(5\pi)$. This proves the analytic asymptotic from the stated identification; locality, convergence of percolation interfaces to radial SLE and that identification are not proved here.</p>

## Shrinking a boundary interval {#section-cardy-density}

<a id="tag-GTW7" data-assertion="proposition" data-title="Cardy's formula gives the boundary density and its Loewner equation"></a>
<p>Assume Cardy's crossing formula for the critical triangular-site scaling limit. For $x&lt;u&lt;v$, let $C_\varepsilon$ be the probability of a connection from $[x,u]$ to $[v-\varepsilon,v+\varepsilon]$. Then</p>
<div class="math-display">$$C_\varepsilon\sim\varepsilon^{1/3}C(x,u,v),\qquad
C(x,u,v)=\frac{\sqrt\pi}{\Gamma(1/3)\Gamma(7/6)}
\left(\frac{u-x}{(v-u)(v-x)}\right)^{1/3}.$$</div>
<p>Moreover, writing $\mathcal L_b=3\partial_u^2+2(x-u)^{-1}\partial_x+2(v-u)^{-1}\partial_v$,</p>
<div class="math-display">$$\mathcal L_b C=\frac{2C}{3(v-u)^2},\qquad
6\partial_u\log C=\frac{2}{u-x}-\frac{2}{u-v}.$$</div>
<p><em>Proof.</em> The cross-ratio is $q=2\varepsilon(u-x)/((v-\varepsilon-x)(v+\varepsilon-u))$. Cardy's formula is</p>
<div class="math-display">$$\frac{\Gamma(2/3)}{\Gamma(1/3)\Gamma(4/3)}q^{1/3}
{}_2F_1(1/3,2/3;4/3;q).$$</div>
<p>The hypergeometric factor tends to one. Gamma duplication and recurrence give $2^{1/3}\Gamma(2/3)/(\Gamma(1/3)\Gamma(4/3))=\sqrt\pi/(\Gamma(1/3)\Gamma(7/6))$, proving the limit. For the differential identities, take the logarithm of the displayed density. Its three derivatives are</p>
<div class="math-display">$$3\partial_x\log C=-\frac1{u-x}+\frac1{v-x},\quad
3\partial_u\log C=\frac1{u-x}+\frac1{v-u},\quad
3\partial_v\log C=-\frac1{v-u}-\frac1{v-x}.$$</div>
<p>Substitution into $C_{uu}/C=(\log C)_{uu}+((\log C)_u)^2$ proves the equation. The same formulas show the boundary asymptotic is uniform on compact sets of distinct ordered marks.</p>

## The stopped conditioning law {#section-stopped-conditioning}

<a id="tag-W3QF" data-assertion="theorem" data-title="The boundary density gives a normalized stopped SLE weight and force-point drift"></a>
<p>Under chordal SLE with parameter $6$, write $U_t=\sqrt6 B_t+u$, $X_t=g_t(x)$, $V_t=g_t(v)$ and $J_t=g_t'(v)$. Stop on a bounded time interval before the marked points collide, localizing so that their gaps, positions and $J_t$ stay in compact admissible sets. Then</p>
<div class="math-display">$$Z_t=\frac{J_t^{1/3}C(X_t,U_t,V_t)}{C(x,u,v)}$$</div>
<p>is a positive martingale with $Z_0=1$. Under the stopped probability measure of density $Z_t$,</p>
<div class="math-display">$$dU_t=\sqrt6\,d\widetilde B_t+
\left(\frac{2}{U_t-X_t}-\frac{2}{U_t-V_t}\right)dt,\qquad
dX_t=\frac{2,dt}{X_t-U_t},\quad dV_t=\frac{2,dt}{V_t-U_t}.$$</div>
<p><em>Proof.</em> The Loewner equation gives $d\log J_t=-2(V_t-U_t)^{-2}dt$. Its contribution cancels the zero-order term in GTW7, and Itô's formula yields</p>
<div class="math-display">$$dZ_t=Z_t\sqrt6\,\partial_u\log C(X_t,U_t,V_t)\,dB_t.$$</div>
<p>Localization makes $Z$ bounded, hence a martingale, and makes its logarithmic diffusion coefficient bounded. Girsanov's theorem therefore replaces $dB_t$ by $d\widetilde B_t+\sqrt6\,\partial_u\log C,dt$. The logarithmic derivative in GTW7 gives the stated drift.</p>
<p>With the SLE domain Markov property and Cardy's formula as inputs, this weight is also the limit of conditioning the interface to hit $[v-\varepsilon,v+\varepsilon]$ before swallowing $x$, on each such stopped sigma-field. Before the stop, the Loewner map is analytic in a uniformly small neighbourhood of $v$, and maps its endpoints to $V_t\pm J_t\varepsilon+O(\varepsilon^2)$ uniformly after further compact localization. The conditional crossing probability divided by its initial value consequently converges uniformly to $Z_t$, by GTW7. Uniform convergence of these densities gives convergence in total variation of the stopped laws. Removing the localization through the terminal collision is a separate task.</p>
<p>For a finite-neighbourhood conditioning event with conditional probability $q_t$ and $D_t=q_t/q_0$, the corresponding identity is $dD_t=D_t\sqrt6\,\partial_u\log q_t,dB_t$, when the only Brownian coordinate is $U_t$. The source's displayed formula for $dD_t$ omits the factor $D_t$; its subsequent logarithmic drift is the intended one. This normalization repair is recorded <a href="/errata/beliaev-izyurov-factorization-2012/#density-martingale-factor">provisionally</a>.</p>

## Conditional and joint equations {#section-joint-operator}

<p>Put $a=5/48$, and use Wirtinger derivatives in the two coordinates $w,\bar w$. Let</p>
<div class="math-display">$$\mathcal L=\mathcal L_b+\frac2{w-u}\partial_w+\frac2{\bar w-u}\partial_{\bar w},\qquad
Q=a\left(\frac1{(w-u)^2}+\frac1{(\bar w-u)^2}\right),\qquad
b=6\partial_u\log C.$$</div>
<p>For a smooth real-valued function $F$, the stopped Itô drift of $|g_t'(w)|^aF(X_t,U_t,V_t,g_t(w))$ under W3QF is $|g_t'(w)|^a(\mathcal L+b\partial_u-Q)F$. Thus the conditional density equation is $(\mathcal L+b\partial_u-Q)F=0$, whenever the probabilistic construction justifies this martingale.</p>

<a id="tag-ES94" data-assertion="proposition" data-title="Multiplying by the boundary density removes the conditioning drift and adds an inverse-square potential"></a>
<p>For every smooth $F$, one has the exact identity</p>
<div class="math-display">$$\left(\mathcal L-Q-\frac2{3(v-u)^2}\right)(CF)
=C(\mathcal L+b\partial_u-Q)F.$$</div>
<p><em>Proof.</em> Only the second-order term differentiates both factors, giving $6C_uF_u$. The remaining derivatives of $C$ contribute $F\mathcal L_bC=2CF/(3(v-u)^2)$ by GTW7. Subtracting this potential and using $Cb=6C_u$ proves the identity.</p>
<p>The square on $v-u$ is essential. Equation (13) and its following proof in the source print the first power instead. The resulting operator differs from the correct one by multiplication by $\tfrac23((v-u)^{-2}-(v-u)^{-1})$. At gap $v-u=2$ it sends any positive solution $CF$ of the corrected equation to $-CF/6$, not zero. This is a <a href="/errata/beliaev-izyurov-factorization-2012/#joint-potential-square">provisional display correction</a>, not a change to the intended force-point law.</p>

## Conformal weights {#section-density-covariance}

<a id="tag-QLZ6" data-assertion="proposition" data-title="The conditional bulk density carries only the bulk conformal weight"></a>
<p>Let $C_D$ denote the boundary density of order $1/3$, let $J_D$ denote the joint boundary/bulk density of orders $1/3$ and $a=5/48$, and set $F_D=J_D/C_D$ where $C_D&gt;0$. Assume the density limits exist with the boundary-neighbourhood limit taken first and transform under the conformally invariant event law. For a conformal map $\varphi:D\to D'$ extending smoothly with nonzero derivative at the boundary mark $v$,</p>
<div class="math-display">$$C_D=|\varphi'(v)|^{1/3}C_{D'},\qquad
J_D=|\varphi'(v)|^{1/3}|\varphi'(w)|^aJ_{D'},\qquad
F_D=|\varphi'(w)|^aF_{D'}.$$</div>
<p>All marks on the right are mapped by $\varphi$. <em>Proof.</em> A boundary interval of radius $\varepsilon$ has image radius $|\varphi'(v)|\varepsilon(1+o(1))$. Conformal radius about $w$ is multiplied exactly by $|\varphi'(w)|$. Taking the two density limits in their specified order gives the first two formulas. The boundary factor cancels in their quotient.</p>
<p>The covariance display after Theorem 1.1 in the source puts both factors on the conditional function $F$. Under the dilation $\varphi(z)=cz$ of the half-plane, the explicit formula (4) has homogeneity $-a$; the extra boundary factor would give $F=c^{1/3}F$. The two-factor formula applies to $CF$, while the conditional function retains only the bulk weight. See the <a href="/errata/beliaev-izyurov-factorization-2012/#conditional-covariance">provisional normalization correction</a>.</p>
<p>The angular asymptotic and stopped change of measure now have written proofs from the stated analytic and SLE inputs. Completing the five-point formula still requires checking its explicit strip solution against ES94, identifying all terminal limits, and supplying an integrable domination for the stopped martingales. Those tasks are distinct from deriving their local differential equation; the present article does not claim to have completed them.</p>

## A comparison away from the conditioned boundary point {#section-local-comparison}

<p>The continuation below separates the remaining analytic argument from its percolation inputs. Throughout, the model is critical site percolation on the triangular lattice in the half-plane, with scaling limits taken before neighbourhoods shrink. Fix $x&lt;u&lt;v$ and $w\in\mathbb H$. Besides the inputs already stated, we use critical-site RSW, convergence of exploration paths, the alternating two-arm exponent, and the usual terminal exploration description specified below. These are not consequences of the angular spectral calculation.</p>

<a id="tag-QHTF" data-assertion="proposition" data-title="Boundary connection conditioning has a bounded effect on events in a distant region"></a>
<p>Let $E_\varepsilon$ be the event that $[x,u]$ connects to $[v-\varepsilon,v+\varepsilon]$. Choose a fixed half-box $B$ centred at $v$, disjoint from $[x,u]$. There are $c&gt;0$ and $\varepsilon_0&gt;0$, depending on the fixed geometry, such that for $0&lt;\varepsilon&lt;\varepsilon_0$, sufficiently fine mesh, and every event $A$ determined by sites outside $B$,</p>
<div class="math-display">$$\mathbb P(A\mid E_\varepsilon)\leq c^{-1}\mathbb P(A).$$</div>
<p><em>Proof.</em> Let $L_\varepsilon$ be the open-arm event from the small interval to the outer boundary of $B$, using sites in $B$ only. Fix the discrete boundary convention with a one-layer margin so that the coordinates determining $L_\varepsilon$ and $A$ are disjoint. Necessarily $E_\varepsilon\subseteq L_\varepsilon$.</p>
<p>Inside $B$, choose a smaller half-annulus surrounding the small interval. An open crossing of this half-annulus from one real boundary segment to the other separates the small interval from the outer boundary of $B$. Add an open corridor joining its inner side to $[x,u]$. These two crossings can be imposed by finitely many overlapping rectangles of fixed aspect ratios; the corridor crosses the separator. RSW bounds the probability of each required crossing below independently of $\varepsilon$ and the fine mesh. Harris association then gives a constant $c&gt;0$ such that their intersection with $L_\varepsilon$ has probability at least $c\mathbb P(L_\varepsilon)$. On that intersection, the arm meets the separator and hence connects to $[x,u]$. Thus $\mathbb P(E_\varepsilon)\geq c\mathbb P(L_\varepsilon)$.</p>
<p>Independence of the disjoint coordinate sets now gives</p>
<div class="math-display">$$\mathbb P(A\mid E_\varepsilon)
\leq\frac{\mathbb P(A\cap L_\varepsilon)}{c\mathbb P(L_\varepsilon)}
=c^{-1}\mathbb P(A).$$</div>
<p>Only the auxiliary open crossings required positive association. The event $A$ itself need not be increasing. In particular it may require arms of opposite colours.</p>

## A moment under the conditioned law {#section-conditioned-moment}

<a id="tag-GXMS" data-assertion="theorem" data-title="The conditioned exploration has finite inverse conformal-radius moments below one quarter"></a>
<p>Assume convergence of critical triangular-site explorations and the continuum alternating two-arm bound: for every $q&lt;1/4$ and fixed outer radius $R$, the limiting probability of an open and a closed arm across a bulk annulus of radii $r,R$ is at most $C_q(r/R)^q$. Let $\gamma$ have the conditioned law of W3QF, up to $\tau$, the first swallowing of $w$ or collision with $v$. Set</p>
<div class="math-display">$$\rho_t=\frac{2\operatorname{Im}g_t(w)}{|g_t'(w)|},\qquad
\rho_\tau=\lim_{t\uparrow\tau}\rho_t.$$</div>
<p>Then, for every $0&lt;p&lt;1/4$,</p>
<div class="math-display">$$\mathbb E_{\mathrm{cond}}[\rho_\tau^{-p}]&lt;\infty.$$</div>
<p><em>Proof.</em> Choose a disk $B_R(w)$ lying in the half-plane and disjoint from the half-box in QHTF. The first entrance of a discrete exploration into $B_r(w)$ forces an open and a closed arm across $B_R(w)\setminus B_{2r}(w)$, once the mesh is small compared with $r$. They run along the two sides of the exploration up to its first entrance. The arm event depends only on sites in this bulk annulus, so QHTF bounds its probability under $E_\varepsilon$ by a constant times its unconditioned probability.</p>
<p>Pass first to the mesh limit with $r,R,\varepsilon$ fixed, then to the boundary-conditioning limit on each compact stopped sigma-field of W3QF. One may use entrance into a slightly larger open disk to pass a path-hitting inequality through weak convergence; the harmless enlargement is absorbed into the factor $2r$. Exhaust the compact stops. The constants do not depend on the stop or on $\varepsilon$. For every $q&lt;1/4$ this proves</p>
<div class="math-display">$$\mathbb P_{\mathrm{cond}}\!\left(\operatorname{dist}(w,\gamma[0,\tau))&lt;r\right)
\leq C_q(r/R)^q,\qquad 0&lt;r&lt;R/4.$$</div>
<p>The conformal radii decrease with the domains. Koebe's theorem gives $\operatorname{dist}(w,\partial D_t)\leq\rho_t$, where $D_t$ is the unbounded unexplored component before $w$ is swallowed. For $r&lt;\operatorname{Im}w$, the event $\rho_\tau&lt;r$ therefore forces the trace to come within $r$ of $w$. The same bound holds for $\mathbb P(\rho_\tau&lt;r)$. Choose $p&lt;q&lt;1/4$ and integrate the tail:</p>
<div class="math-display">$$\mathbb E[\rho_\tau^{-p}]
\leq R_0^{-p}+p\int_0^{R_0}r^{-p-1}\mathbb P(\rho_\tau&lt;r)\,dr&lt;\infty$$</div>
<p>for a sufficiently small fixed $R_0$. In particular $\rho_\tau&gt;0$ almost surely. Taking $p=1/8$ shows that the family $\rho_t^{-5/48}$ is bounded in $L^{6/5}$ and dominated by the integrable random variable $\rho_\tau^{-5/48}$.</p>
<p>The two-arm estimate used here is the opposite-colour bulk estimate of Smirnov–Werner, with exponent $1/4$; it is not the monochromatic two-arm exponent. Rohde–Schramm Lemma 6.3 gives the same moment threshold for ordinary chordal SLE with parameter $6$. Its statement does not by itself supply a moment under the conditioned law: local absolute continuity alone is insufficient for that transfer. The comparison above supplies the needed bound without making that inference.</p>

## A bounded form of the strip solution {#section-strip-bound}

<p>Write $a=5/48$, $K_4=18/(5\pi)$ and</p>
<div class="math-display">$$\mathcal F(q)={}_2F_1(-1/2,-1/3;7/6;q),\qquad
F_1=\mathcal F(1),\qquad
\psi_*(X)=\frac{e^{\pi X/3}\mathcal F(e^{-2\pi X})}{F_1}.$$</div>
<p>Let $\Psi$ map $(\mathbb H;x,u,v)$ to the half-strip with marked points $(i,0,\infty)$, and put $(X,Y)=(\operatorname{Re}\Psi(w),\operatorname{Im}\Psi(w))$. The candidate in the source is</p>
<div class="math-display">$$H(x,u,v,w)=K_5|\Psi'(w)|^a G(X,Y),\qquad
K_5=\frac{K_4\pi^a}{2^aF_1},$$</div>
<div class="math-display">$$G(X,Y)=e^{\pi X/3}\mathcal F(e^{-2\pi X})\sinh(\pi X)^{-1/3}
\left(\frac{\sinh^2(\pi X)\sin^2(\pi Y)}{\sinh^2(\pi X)+\sin^2(\pi Y)}\right)^{11/96}.$$</div>

<a id="tag-RD0Q" data-assertion="proposition" data-title="The strip solution is uniformly bounded after removing the conformal-radius weight"></a>
<p>If $\omega$ is the harmonic measure of $[x,u]$ from $w$, then</p>
<div class="math-display">$$H=K_4(2\operatorname{Im}w)^{-a}\psi_*(X)\sin^{1/3}(\pi\omega/2),\qquad
0\leq(2\operatorname{Im}w)^aH\leq 2^{1/3}K_4.$$</div>
<p><em>Proof.</em> The first identity is the cancellation V456. Put $S=\sinh(\pi X)$ and $T=\sin(\pi Y)$. The same calculation gives $\sin(\pi\omega/2)=T/(S^2+T^2)^{1/2}$. The positive coefficients of $\mathcal F$ give $0&lt;\mathcal F(q)\leq F_1$ for $0\leq q\leq1$. Since $0&lt;T\leq1$,</p>
<div class="math-display">$$e^{\pi X}\frac{T}{\sqrt{S^2+T^2}}
\leq\frac{e^{\pi X}}{\cosh(\pi X)}\leq2.$$</div>
<p>Taking cube roots proves the bound. Consequently, for every stopped exploration,</p>
<div class="math-display">$$0\leq |g_t'(w)|^a H(X_t,U_t,V_t,g_t(w))
\leq 2^{1/3}K_4\rho_t^{-a}\leq2^{1/3}K_4\rho_\tau^{-a}.$$</div>
<p>Here capital $X_t=g_t(x)$ is the boundary force point; the strip abscissa remains $\operatorname{Re}\Psi_t(g_t(w))$.</p>

## Verification of the local equation {#section-candidate-equation}

<a id="tag-AGJ2" data-assertion="proposition" data-title="The strip candidate satisfies the conditional SLE equation"></a>
<p>Assume the stopped Möbius coordinate-change theorem for SLE with force points. Then the smooth candidate $H$ satisfies $(\mathcal L+b\partial_u-Q)H=0$ on the configuration space $x&lt;u&lt;v$, $w\in\mathbb H$. Thus $|g_t'(w)|^aH(X_t,U_t,V_t,g_t(w))$ is a local martingale under W3QF.</p>
<p><em>Proof.</em> The coordinate-change theorem of Schramm–Wilson applies because the two force weights sum to $2-2=0=6-6$. Map $v$ to infinity, then normalize $(x,u)=(0,1)$. The force at infinity contributes no drift. The candidate transforms with the bulk weight $a$, directly from its definition by $\Psi$. Therefore the local martingale calculation in these coordinates transfers to every finite configuration, up to a positive time change and compact stopping before the mapped target is swallowed.</p>
<p>For the normalized calculation write $z=w$, $D=z\partial_z+\bar z\partial_{\bar z}$, and $h(z)=H(0,1,\infty,z)$. Translation and homogeneity give $\partial_uH=-(a+D)h$, $\partial_u^2H=(a+D+1)(a+D)h$ and $\partial_xH=(a+D-\partial_z-\partial_{\bar z})h$ at this configuration. The conditional equation reduces to $\mathcal Ph=0$, where</p>
<div class="math-display">$$\mathcal P=3D^2+(6a-1)D+(3a^2-a)
+\frac{2z}{z-1}\partial_z+\frac{2\bar z}{\bar z-1}\partial_{\bar z}
-a\left((z-1)^{-2}+(\bar z-1)^{-2}\right).$$</div>
<p>Put $U=\pi X$, $V=\pi Y$, so that $z=(1+\cosh(U+iV))/2$. To keep the differentiation short, set $S=\sinh U$, $C=\cosh U$, $T=\sin V$, $c=\cos V$, $A=C-c$, and $Q_0=S^2+T^2$. The candidate $h$ is a constant times $k(U,V)f(U)$, with</p>
<div class="math-display">$$k=e^{U/3}S^{-a}T^{11/48}Q_0^{-1/6},\qquad f(U)=\mathcal F(e^{-2U}).$$</div>
<p>The chain rule gives</p>
<div class="math-display">$$D=\frac{S\partial_U-T\partial_V}{A},\qquad
\frac{k_U}{k}=\frac13-a\frac CS-\frac{SC}{3Q_0},\qquad
\frac{k_V}{k}=\frac{11c}{48T}-\frac{Tc}{3Q_0}.$$</div>
<p>For clarity, the first-order vector field $2z(z-1)^{-1}\partial_z+2\bar z(\bar z-1)^{-1}\partial_{\bar z}$ has coefficients</p>
<div class="math-display">$$b_U=\frac{4S}{Q_0}\left(c+\frac{2(C(2c^2-1)-c)}{A^2}\right),\qquad
b_V=-\frac{4T}{Q_0}\left(C+\frac{2((C^2+S^2)c-C)}{A^2}\right),$$</div>
<p>and the subtracted potential is $8a((Cc-1)^2-S^2T^2)/A^4$. Substituting these three expressions and collecting $f''$, $f'$ and $f$ gives</p>
<div class="math-display">$$\mathcal P(kf)=\frac{3kS^2}{A^2}
\left[f''+\left(\frac23-\coth U\right)f'
+\frac{1-\coth U}{3}f\right].$$</div>
<p>The hypergeometric equation is</p>
<div class="math-display">$$q(1-q)\mathcal F''(q)+\left(\frac76-\frac q6\right)\mathcal F'(q)-\frac16\mathcal F(q)=0.$$</div>
<p>With $q=e^{-2U}$, $f'=-2q\mathcal F'$ and $f''=4q^2\mathcal F''+4q\mathcal F'$. The bracket is $4q/(1-q)$ times the last displayed left-hand side, and vanishes. This proves the equation by direct differentiation of the explicit candidate, without assuming differentiability of a probabilistically defined density.</p>

## Terminal values and optional stopping {#section-terminal-formula}

<p>We use the terminal exploration description in Beliaev–Izyurov section 3 as a separate input. The conditioned interface avoids $x$ until it reaches $v$; at $\tau$ its component containing $w$ has a Carathéodory limit $D_\tau$. The arc attached to $[x,u]$ is empty when the interface disconnects $w$ on its closed side, the whole accessible boundary when it disconnects $w$ on its open side, and the exposed attached arc when it reaches $v$ first. Harmonic measures converge to the measure $\omega_\tau$ of this arc. In normalized coordinates the bulk point approaches $1$ in the first two cases; in the last case the Möbius normalization sending the three marks to $0,1,\infty$ sends it to $0$. These assertions concern the geometry and limiting percolation law; W3QF proves its stopped density but does not by itself prove this terminal description.</p>

<a id="tag-X364" data-assertion="proposition" data-title="All terminal cases of the strip candidate have the same harmonic-measure expression"></a>
<p>Under this terminal geometry and the hypotheses of GXMS,</p>
<div class="math-display">$$\lim_{t\uparrow\tau}|g_t'(w)|^aH(X_t,U_t,V_t,g_t(w))
=K_4\rho_\tau^{-a}\sin^{1/3}(\pi\omega_\tau/2)$$</div>
<p>almost surely and in $L^1$.</p>
<p><em>Proof.</em> The inverse strip map is $z=(1+\cosh(\pi\zeta))/2$. Thus a normalized bulk point tending to $1$ gives $\zeta\to0$, while a point tending to $0$ gives $\zeta\to i$. In all three terminal cases the strip abscissa tends to zero. By ZZ9Q, $\psi_*(X)\to1$. The first identity of RD0Q therefore gives the stated limit, using convergence of the harmonic measure and conformal radius. The expression is zero for the empty arc and $K_4\rho_\tau^{-a}$ for the whole boundary. The bound in RD0Q and the moment in GXMS give dominated convergence, hence convergence in $L^1$ as well.</p>

<a id="tag-SQJF" data-assertion="theorem" data-title="The five-point density follows from the explicit candidate and terminal exploration inputs"></a>
<p>Assume the percolation, SLE and terminal geometry inputs above. Assume also the terminal domain Markov identification: after the boundary interval shrinks, conditional on the explored interface the remaining percolation in $D_\tau$ is critical percolation attached to the indicated boundary arc. For $0&lt;\varepsilon&lt;\rho_\tau$, its probability that the remaining conformal radius about $w$ is less than $\varepsilon$ is</p>
<div class="math-display">$$h\left(2\pi\omega_\tau,\log(\rho_\tau/\varepsilon)\right).$$</div>
<p>Then the conditional bulk density exists and equals the strip candidate:</p>
<div class="math-display">$$\lim_{\varepsilon\downarrow0}\varepsilon^{-5/48}
\mathbb P_{\mathrm{cond}}(r(w)&lt;\varepsilon)
=H(x,u,v,w)
=K_4\mathbb E_{\mathrm{cond}}\!\left[\rho_\tau^{-5/48}\sin^{1/3}(\pi\omega_\tau/2)\right].$$</div>
<p>The boundary-neighbourhood limit is taken before this bulk-neighbourhood limit; both follow the mesh limit. Multiplying by GTW7 gives the joint boundary/bulk density.</p>
<p><em>Proof.</em> By DCSM, $h(\theta,s)\leq C e^{-as}$ for $s\geq1$, uniformly in $\theta$. The trivial bound $h\leq1$ extends this estimate to $s\geq0$ by increasing $C$. If $\varepsilon&lt;\rho_\tau$, the normalized conditional probability given the interface is consequently at most $C\rho_\tau^{-a}$. If $\varepsilon\geq\rho_\tau$, it is at most $\varepsilon^{-a}\leq\rho_\tau^{-a}$. The latter case requires no formula for the residual event. Q4NI gives the pointwise normalized limit $K_4\rho_\tau^{-a}\sin^{1/3}(\pi\omega_\tau/2)$, including the empty arc by zero. The moment estimate allows dominated convergence and proves the expectation formula.</p>
<p>On the other hand, AGJ2 makes $M_t=|g_t'(w)|^aH(X_t,U_t,V_t,g_t(w))$ a local martingale. Choose compact localizing stops increasing to $\tau$, also truncating time if needed. At each stop the martingale is bounded and has expectation $M_0=H(x,u,v,w)$. The single integrable bound of RD0Q applies to all these stops. Passing to the terminal limit by X364 proves that $H$ has the same expectation representation. This identifies the candidate and the density.</p>
<p>The analytic solution, terminal asymptotics and uniform integrability have now been supplied under the listed inputs. The foundational exploration convergence, the terminal domain Markov identification, the radial-SLE interpretation of $h$, RSW, the two-arm exponent and the SLE coordinate-change theorem remain literature inputs. In particular this continuation does not infer a full terminal conditioning theorem from convergence on compact stopped sigma-fields, or claim a Lean formalisation of any of these inputs.</p>


<p>The ordinary-SLE comparison cited above now has a <a href="/articles/sle-conformal-radius/#section-exact-moments">complete conformal-radius moment argument</a>, including the sharp exponent and the case $\kappa=8$. It uses a radius-clock angular diffusion and justifies optional stopping by a positive integral representation. The conditioned estimate GXMS continues to use its own percolation comparison.</p>


## The first force-point collision {#section-force-collision}

<p>The stopped law W3QF leaves a concrete question about its endpoint. With $X_0=x&lt;U_0=u&lt;V_0=v$, consider the maximal solution of</p>
<div class="math-display">$$dU_t=\sqrt6\,dW_t+\left(\frac2{U_t-X_t}+\frac2{V_t-U_t}\right)dt,
\qquad dX_t=-\frac2{U_t-X_t}\,dt,
\qquad dV_t=\frac2{V_t-U_t}\,dt.$$</div>
<p>Let $T$ be its lifetime in $X&lt;U&lt;V$, and write $A=U-X$ and $B=V-U$. Local strong existence and uniqueness hold because the coefficients are locally Lipschitz in this open region. Subtraction gives</p>
<div class="math-display">$$dA_t=\sqrt6\,dW_t+\left(\frac4{A_t}+\frac2{B_t}\right)dt,
\qquad dB_t=-\sqrt6\,dW_t-\frac2{A_t}\,dt.$$</div>

<a id="tag-HOKP" data-assertion="theorem" data-title="The two-force diffusion has finite lifetime and approaches only the right force point"></a>
<p>Almost surely $0&lt;T&lt;\infty$, $\inf_{0\leq t&lt;T}A_t&gt;0$ and $B_t\to0$ as $t\uparrow T$. In the coupling with its driving Brownian motion,</p>
<div class="math-display">$$T\leq H_{B_0/\sqrt6},\qquad H_c:=\inf\{t\geq0:W_t=c\}.$$</div>
<p><em>Proof.</em> Use the same Brownian motion to solve $dR_t=\sqrt6\,dW_t+4R_t^{-1}dt$, $R_0=A_0$. This comparison process remains positive and finite for all finite times. Here is a direct verification. Its generator is $3\partial_r^2+4r^{-1}\partial_r$, so $R^{-1/3}$ is a local martingale and $R^2-14t$ is a local martingale. Stop on leaving $(\delta,M)$ and at deterministic time $N$. Optional stopping bounds the probabilities of an exit at the lower and upper boundaries by</p>
<div class="math-display">$$\left(\frac{\delta}{A_0}\right)^{1/3}
\quad\text{and}\quad \frac{A_0^2+14N}{M^2},$$</div>
<p>respectively. Letting $\delta\downarrow0$ and $M\to\infty$ excludes a finite lifetime. In particular, $R$ has a positive minimum on every compact time interval.</p>
<p>Before $T$, the Brownian terms cancel in $D=A-R$, leaving</p>
<div class="math-display">$$D'=-\frac{4D}{AR}+\frac2B,\qquad D_0=0.$$</div>
<p>An integrating factor gives $D\geq0$. Thus $A\geq R$ throughout the lifetime. On the other hand,</p>
<div class="math-display">$$B_t=B_0-\sqrt6\,W_t-2\int_0^t\frac{ds}{A_s}
\leq B_0-\sqrt6\,W_t.$$</div>
<p>The positive solution cannot survive past $H_{B_0/\sqrt6}$, which is finite almost surely. Since $R$ has a positive minimum up to this random finite time, $A$ is bounded away from zero and $\int_0^T A_s^{-1}ds&lt;\infty$. The displayed identity therefore gives a finite nonnegative limit for $B_t$. If this limit were positive, both gap drifts would be bounded near $T$; the Brownian path and the positions would remain finite, and local existence would extend the solution. Hence the limit is zero, proving the assertion.</p>
<p>This is an assertion about the Loewner driving system. Identifying the collision with a visit of a continuous trace to the original boundary point still requires the trace interpretation.</p>

## Integrating through the collision {#section-force-endpoint}

<a id="tag-QF08" data-assertion="theorem" data-title="The force-point drifts are integrable and the driving system has a finite continuous endpoint"></a>
<p>For the diffusion above, almost surely</p>
<div class="math-display">$$\int_0^T\left(\frac1{A_t}+\frac1{B_t}\right)dt&lt;\infty.$$</div>
<p>The three positions have finite limits, with</p>
<div class="math-display">$$X_T&lt;U_T=V_T,
\qquad U_T-X_T=v-x+2\int_0^T\left(\frac1{A_t}+\frac1{B_t}\right)dt\geq v-x.$$</div>
<p><em>Proof.</em> HOKP already gives the integral of $A^{-1}$. For the other gap use $\psi(b)=b\log b$, extended by $\psi(0)=0$. Itô's formula yields</p>
<div class="math-display">$$d\psi(B_t)=-\sqrt6(1+\log B_t)\,dW_t
+\left(\frac3{B_t}-\frac2{A_t}(1+\log B_t)\right)dt.$$</div>
<p>Fix $N,M,m&gt;0$ with $B_0&lt;M$ and $A_0&gt;m$. For $0&lt;\delta&lt;B_0$, stop at time $N$, on $B=M$, on $A=m$, or on $B=\delta$, whichever happens first. Call this stop $\theta_\delta$. Before it, the drift in the last display is at least $3/B-C$, where</p>
<div class="math-display">$$C=\frac2m\max\{1+\log M,0\}.$$</div>
<p>The stopped stochastic integral has zero expectation: its integrand is bounded for fixed $\delta$. Consequently</p>
<div class="math-display">$$3\,\mathbb E\int_0^{\theta_\delta}\frac{dt}{B_t}
\leq\sup_{0\leq b\leq M}\psi(b)-\psi(B_0)+CN.$$</div>
<p>The bound is independent of $\delta$. Monotone convergence as $\delta\downarrow0$ proves integrability up to the minimum of the other stops and $T$. Now let $N,M\to\infty$ and $m\downarrow0$ along a countable sequence. These localizations cover the entire path up to $T$: HOKP gives finite $T$ and a positive lower bound for $A$, while $B_t\leq B_0+\sqrt6\sup_{s\leq T}|W_s|$. Thus $\int_0^T B_t^{-1}dt$ is finite almost surely.</p>
<p>Both drifts in the position equations are now integrable. In particular,</p>
<div class="math-display">$$X_T=x-2\int_0^T\frac{dt}{A_t},\qquad
V_T=v+2\int_0^T\frac{dt}{B_t},\qquad
U_T=u+\sqrt6W_T+2\int_0^T\left(\frac1{A_t}+\frac1{B_t}\right)dt.$$</div>
<p>The limit $B_T=0$ gives $U_T=V_T$. Finally $V-X=A+B$ is increasing, with derivative $2/A+2/B$, proving the displayed separation from $X_T$. The driving function therefore extends continuously to the collision, even though its drift is singular there.</p>

## A bound on the collision time {#section-force-time-tail}

<a id="tag-6EPL" data-assertion="corollary" data-title="The collision time has a Brownian first-passage tail bound and finite moments below one half"></a>
<p>For every $t&gt;0$, with $b=v-u$,</p>
<div class="math-display">$$\mathbb P(T&gt;t)\leq
2\Phi\left(\frac b{\sqrt{6t}}\right)-1
\leq\min\left\{1,\frac b{\sqrt{3\pi t}}\right\},$$</div>
<p>where $\Phi$ is the standard normal distribution function. For $0&lt;p&lt;1/2$,</p>
<div class="math-display">$$\mathbb E[T^p]\leq
\left(\frac{b^2}{12}\right)^p\frac{\Gamma(1/2-p)}{\sqrt\pi}.$$</div>
<p><em>Proof.</em> HOKP bounds $T$ by $H_c$ with $c=b/\sqrt6$. The reflection principle gives $\mathbb P(H_c&gt;t)=2\Phi(c/\sqrt t)-1$. Bounding the normal density by $1/\sqrt{2\pi}$ proves the second inequality. Differentiation gives the first-passage density</p>
<div class="math-display">$$\frac{c}{\sqrt{2\pi}}t^{-3/2}e^{-c^2/(2t)}.$$</div>
<p>Integrating $t^p$ against this density and substituting $s=c^2/(2t)$ gives $\mathbb E[H_c^p]=(c^2/2)^p\Gamma(1/2-p)/\sqrt\pi$. This proves the bound. It does not assert divergence of moments of $T$ at or above $1/2$.</p>

## Completing the stopped driving law {#section-force-law}

<a id="tag-0SPP" data-assertion="proposition" data-title="The compact stopped change-of-measure laws determine a unique continuous driving system absorbed at collision"></a>
<p>The local laws in W3QF determine a unique law of $(X,U,V)$ that is continuous up to its first collision and is held constant thereafter. This law is the maximal two-force solution above, completed at the finite time $T$. For any increasing exhaustion by compact stops $\sigma_n\uparrow T$, the paths stopped at $\sigma_n$ converge almost surely to the path stopped at $T$, uniformly on every bounded time interval.</p>
<p><em>Proof.</em> Solve the locally Lipschitz system with a Brownian driver up to its maximal lifetime. HOKP and QF08 give a finite lifetime and a continuous finite endpoint, so constant continuation defines a probability law on continuous paths. For example, one may stop when time reaches $n$, either gap reaches $1/n$, the sum of absolute positions reaches $n$, or $J_t=g_t'(v)$ reaches $1/n$, where</p>
<div class="math-display">$$J_t=\exp\left(-2\int_0^t B_s^{-2}\,ds\right),\qquad t&lt;T.$$</div>
<p>Start the exhaustion at an index containing the initial configuration. On each compact subinterval of $[0,T)$, the gaps and $J$ have positive minima and all positions are bounded. Thus these stops increase to $T$. The Girsanov calculation in W3QF and uniqueness of the stopped SDE identify each restriction of the constructed law with the normalized stopped weight there.</p>
<p>Pathwise uniqueness holds up to each compact stop, and hence throughout $[0,T)$. Continuity fixes the endpoint, and absorption fixes everything after it. More generally, two continuous absorbed extensions with the same exhaustive compact stopped laws have the same law: their stopped paths converge uniformly on bounded intervals to the completed paths, so expectations of bounded continuous path functionals agree in the limit. The asserted uniform convergence follows from uniform continuity of the completed path on compact intervals and $\sigma_n\uparrow T$.</p>
<p>This constructs and identifies the stopped driving diffusion. It does not interchange the boundary-conditioning limit with $n\to\infty$: convergence of finite-neighbourhood laws at each fixed compact stop does not by itself imply convergence at their terminal times. The trace geometry, the residual percolation law at the terminal domain, and their convergence remain the explicit inputs in X364 and SQJF.</p>

## The coordinate change in the candidate proof {#section-proved-coordinate-change}

<a id="tag-8Q5E" data-assertion="proposition" data-title="The explicit strip candidate satisfies the full local equation by the proved chordal coordinate change"></a>
<p>The smooth candidate $H$ defined above satisfies $(\mathcal L+b\partial_u-Q)H=0$ for every $x&lt;u&lt;v$, $w\in\mathbb H$. Accordingly, $|g_t'(w)|^{5/48}H(X_t,U_t,V_t,g_t(w))$ is a local martingale for the two-force driving system, stopped before swallowing $w$ or colliding with a force point. The coordinate-change step follows from C6T0, 6RZ1 and 0INI.</p>
<p><em>Proof.</em> At a fixed initial configuration choose</p>
<div class="math-display">$$m(z)=\frac{(z-x)(u-v)}{(z-v)(u-x)}.$$</div>
<p>This maps $\mathbb H$ to itself and sends $(x,u,v)$ to $(0,1,\infty)$. The two weights sum to zero, which is $\kappa-6$ for $\kappa=6$. By 6RZ1 the transformed driving system has just the finite force of weight $2$ at the image of $x$; the force at infinity contributes zero. The stopping restriction is exactly the one needed here, since the new target is $v$.</p>
<p>Uniqueness of the normalized strip map gives $\Psi_{m(x),m(u),m(v)}\circ m=\Psi_{x,u,v}$. Differentiation proves the bulk covariance $H(x,u,v,w)=|m'(w)|^{5/48}H(m(x),m(u),m(v),m(w))$. In the normalized coordinates, the explicit calculation in <a href="#section-candidate-equation">the local-equation section</a> reduces the drift to</p>
<div class="math-display">$$\frac{3k\sinh^2 U}{(\cosh U-\cos V)^2}
\left[f''+\left(\frac23-\coth U\right)f'
+\frac{1-\coth U}{3}f\right],$$</div>
<p>where $f(U)={}_2F_1(-1/2,-1/3;7/6;e^{-2U})$ and $k$ is the explicit prefactor there. The hypergeometric equation makes the bracket zero. Translation and positive scaling extend this calculation from $(0,1,\infty)$ to every ordered pair of finite marks with the third at infinity. Thus the image observable is a local martingale throughout its stopped configuration space. The pathwise identity 0INI transfers it to the original coordinates.</p>
<p>Applying Itô's formula to this smooth explicit observable identifies its drift with $|g_t'(w)|^{5/48}(\mathcal L+b\partial_u-Q)H$. Since the initial configuration was arbitrary, the displayed differential equation follows everywhere. The older assertion AGJ2 and its normalized calculation are retained; the coordinate-change result it used as an input is now proved in the required chordal boundary case. The terminal conditioning and percolation inputs of SQJF are unaffected.</p>
