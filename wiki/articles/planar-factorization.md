---
{
  "id": "planar-factorization",
  "title": "From neighbourhood connections to point connections",
  "subtitle": "Separating circuits, relative errors and planar factorization",
  "kind": "method",
  "category": "General theory",
  "summary": "A coupling across nested annuli makes local connection costs independent of distant conditions. Uniform control of the remaining one-arm probability turns coupling success into a relative estimate, which transfers continuum factorization formulas to lattice sites.",
  "context": [
    "Critical independent site percolation on the triangular lattice in the closed upper half-plane, with free boundary.",
    "Critical triangular-site RSW is an explicit external input. The continuum density formulas used at the end are separate cited inputs.",
    "Marked points stay fixed and distinct as the mesh tends to zero; a bulk mark stays strictly above the real boundary."
  ],
  "related": ["adaptive-three-point", "critical-exponents", "disjoint-occurrence", "stopped-exploration"],
  "sourceIds": ["conijn-factorization-2015", "beliaev-izyurov-factorization-2012"],
  "aliases": ["Conijn coupling", "one-arm-like events", "boundary factorization", "continuum to discrete"],
  "prototypeUses": []
}
---

## Conditions separated by an open circuit {#section-local-events}

<p>Write $\mu_\eta$ for critical triangular-site percolation of mesh $\eta$ in $\overline{\mathbb H}$. Boxes use the maximum norm and are intersected with this half-plane. A marked site $z$ is either on the real boundary, or is a bulk site with $B_C(z)\subset\mathbb H$. A separator is a simple circuit around the inner box in the bulk case, or a simple path from the real boundary to itself enclosing the inner half-box in the boundary case. Its bounded and unbounded sides are denoted by $\operatorname{int}\gamma$ and $\operatorname{ext}\gamma$; neither includes the sites of $\gamma$.</p>
<p>Fixed Euclidean marks are represented by nearest lattice sites, with boundary marks represented by boundary sites. Intervals are interpreted by the lattice hexagons they meet, and cluster obstacles by the corresponding closed hexagons. All local comparisons allow a fixed margin of several mesh lengths.</p>
<p>For an increasing measurable event $V$ and a set of sites $D$, let $V_D$ be the restrictions to $D$ that can be extended to an element of $V$. Equivalently, set every site outside $D$ open and test $V$. This description proves measurability and gives $(V_D)_E=V_E$ whenever $E\subset D$.</p>

<a id="tag-83WA" data-assertion="definition" data-title="Local one-arm conditions, point versions and comparable exterior conditions"></a>
<p>Let $0&lt;s&lt;C$ and let $I_s$ be the short horizontal segment from $z$ to $z+s/8$, interpreted by the hexagons it meets. An increasing event $V$ is a local one-arm condition at scales $(s,C)$ if it forces an open path from $B_s(z)$ to outside $B_C(z)$, and every separator $\gamma$ in $B_C(z)\setminus B_s(z)$ satisfies</p>
<div class="math-display">$$V\cap\{\gamma\text{ open}\}
=V_{\operatorname{int}\gamma}\cap V_{\operatorname{ext}\gamma}\cap\{\gamma\text{ open}\},\qquad
\{I_s\leftrightarrow\gamma\}\subset V_{\operatorname{int}\gamma}.$$</div>
<p>Interior connection events in this formula wire the target sites of $\gamma$ open. A point version is an increasing event $V^\bullet$ such that</p>
<div class="math-display">$$V^\bullet\subset V\cap\{z\leftrightarrow B_C(z)^c\},\qquad
\{\gamma\text{ open}\}\cap V_{\operatorname{ext}\gamma}\cap\{z\leftrightarrow\gamma\}\subset V^\bullet.$$</div>
<p>Two local conditions $V,W$ are comparable if $V_{B_C(z)}=W_{B_C(z)}$. Their projections then agree on every subset of $B_C(z)$, in particular inside every separator under consideration. These are the conditions of Conijn's Definitions 7–9, restricted to boundary-centred or entirely bulk boxes. This restriction suffices for fixed marked points by reducing $C$.</p>
<p>On an open separator, the point-version conditions give the exact identity</p>
<div class="math-display">$$V^\bullet\cap\{\gamma\text{ open}\}
=V_{\operatorname{ext}\gamma}\cap\{\gamma\text{ open}\}\cap\{z\leftrightarrow\gamma\}.$$</div>
<p>Indeed, a path from $z$ to outside $B_C$ must hit $\gamma$, and the converse is the lower point-version condition. Thus the interior point event is the same for every point version once a separating open curve has been found.</p>

## The geometric input {#section-site-rsw}

<p>We use critical triangular-site RSW: every fixed-aspect-ratio rectangle has an open crossing with probability bounded below uniformly as the mesh becomes small compared with its shorter side. Boundary half-boxes use rectangles contained in the half-plane. This is a cited crossing input, not the square-lattice bond statement WD31. Harris association follows from the product law, also after any fixed set of other sites has been specified.</p>
<p>Here are the gluing consequences used below, with constants independent of $s,C,z,\eta$ in the two geometries above, provided $\eta&lt;c_*s$ for a sufficiently small absolute $c_*$. There is a uniformly positive probability of an open separator in $B_{2s}\setminus B_s$. If $\gamma$ surrounds $B_s$ and lies inside $B_{2s}$, its wired interior law satisfies $\mu_\eta^\gamma(I_s\leftrightarrow\gamma)\geq c_0$. If instead $\gamma$ lies outside $B_{4s}$, then</p>
<div class="math-display">$$\mu_\eta^\gamma(I_s\leftrightarrow\gamma)\geq c_0\mu_\eta^\gamma(B_s\leftrightarrow\gamma).$$</div>
<p>Finally, with $a_\eta(r)=\mu_\eta(z\leftrightarrow B_r(z)^c)$, one has $a_\eta(2s)\geq c_1a_\eta(s)$.</p>
<p>To obtain the separators, join crossings of four overlapping rectangular strips around a box, or three strips around a half-box. Adjacent crossings meet in their common corner square. Their union contains the required simple separating curve after loops are erased. The strips can be chosen with fixed positive margins from the prescribed inner and outer boundaries, so rounding to lattice cells preserves bounded aspect ratios when $\eta/s$ is small.</p>
<p>A vertical crossing of a rectangle of width $s/8$ based on $I_s$, reaching height $3s$ above $z$, has uniformly positive probability and must hit every separator inside $B_{2s}$. This proves the first wired estimate. For the second, require such a crossing and a separator in $B_{2s}\setminus B_s$, together with the existing connection from $B_s$ to the distant $\gamma$. Both paths hit the small separator and hence join. All added events are increasing, so Harris gives a constant multiple of the original connection probability. The same construction with a separator between radii $s/4$ and $s/2$ joins an arm from $z$ of length $s$ to a crossing reaching beyond $2s$, proving doubling. The target is wired only at its boundary; none of these estimates conditions an arbitrary arm endpoint to join a prescribed crossing.</p>

## The cost of reaching the marked site {#section-completion}

<a id="tag-R77Z" data-assertion="theorem" data-title="Point completion under an arbitrary admissible exterior has the ordinary one-arm scale"></a>
<p>Under the preceding RSW input, let $V$ be a local one-arm condition, let $V^\bullet$ be a point version, and suppose $16s&lt;C$. Fix the configuration $\xi$ outside $B_r(z)$, where $4s\leq r&lt;16s$, with $\mu_\eta(V\mid\xi)&gt;0$. There are absolute constants $c_2,C_2&gt;0$ such that</p>
<div class="math-display">$$c_2a_\eta(2s)\leq\mu_\eta(V^\bullet\mid V,\xi)\leq C_2a_\eta(2s).$$</div>
<p>The constants are uniform in the local condition, its point version and the admissible exterior. Conditioning on $\xi$ means the product law on the finitely many unrevealed sites, not division by the probability of a single infinite configuration.</p>
<p><em>Proof.</em> Let $B$ be the event that an open separator exists between radii $s$ and $2s$, and reveal its outermost such separator $\Gamma$. The event $\{\Gamma=\gamma\}$ is determined by the sites of $\gamma$ and those outside it: any competing separator farther out is detected there. The strict interior is therefore a fresh product configuration with $\gamma$ wired open. Conditional on $V$ as well, this interior law is conditioned only on $V_{\operatorname{int}\gamma}$, by the factorization in 83WA. On any exterior with positive weight, the conditional point probability is exactly</p>
<div class="math-display">$$\frac{\mu_\eta^\gamma(z\leftrightarrow\gamma)}{\mu_\eta^\gamma(V_{\operatorname{int}\gamma})}.$$</div>
<p>The numerator event implies the denominator event since $z\in I_s$. The denominator lies in $[c_0,1]$ by the seed-segment estimate. An arm to outside $B_{2s}$ must hit $\gamma$, while a connection to $\gamma$ contains an arm to outside $B_{s/2}$ once $\eta&lt;c_*s$. Two applications of doubling compare $a_\eta(s/2)$ with $a_\eta(2s)$. Consequently the displayed quotient lies between $a_\eta(2s)$ and a fixed multiple of $a_\eta(2s)$.</p>
<p>It remains to insert $B$. Under the product law with exterior $\xi$ fixed, Harris gives</p>
<div class="math-display">$$\mu_\eta(B\cap V^\bullet\mid\xi)\geq\mu_\eta(B)\mu_\eta(V^\bullet\mid\xi),\qquad
\mu_\eta(B\cap V\mid\xi)\geq\mu_\eta(B)\mu_\eta(V\mid\xi).$$</div>
<p>The first inequality uses that $V^\bullet$ is increasing after restriction and that $B$ uses only unconditioned sites; it does not assert positive association under the law conditioned on $V$. Divide by $\mu_\eta(V\mid\xi)$, and use the positive lower bound on $\mu_\eta(B)$. Averaging the interior quotient over the possible $\Gamma$ now gives both bounds.</p>

## Coupling from the outside inward {#section-annular-coupling}

<a id="tag-XP8A" data-assertion="theorem" data-title="Comparable local conditions have asymptotically equal point-completion probabilities"></a>
<p>Assume the same RSW input and fix $C$ and the local geometry. For comparable positive-probability conditions $V,W$ and point versions $V^\bullet,W^\bullet$, uniformly when $\eta&lt;c_*s$ and $s/C$ is sufficiently small,</p>
<div class="math-display">$$\left|\frac{\mu_\eta(V^\bullet\mid V)}{\mu_\eta(W^\bullet\mid W)}-1\right|\leq C_3(s/C)^\beta$$</div>
<p>for constants $C_3,\beta&gt;0$ independent of the two conditions and their point versions.</p>
<p><em>Proof.</em> Put $l_i=4^{-i}C$ and $N=\lfloor\log_4(C/s)\rfloor-2$. At stage $i\in\{0,\ldots,N\}$ use an inner annulus between $l_i/4$ and $l_i/2$ and an outer annulus between $l_i/2$ and $l_i$. Let $\Gamma_I$ be the outermost open separator in the first and $\Gamma_O$ the innermost in the second, taking the value $\varnothing$ when none exists. Separators are revealed by exploring from the relevant side. For fixed nonempty $\gamma,\gamma'$, the event</p>
<div class="math-display">$$D(\gamma,\gamma')=\{\Gamma_I=\gamma,\ \Gamma_O=\gamma',\ \gamma\leftrightarrow\gamma'\}$$</div>
<p>depends only on the region between the two curves, including their sites. Their strict interior and exterior remain independent product configurations. The choice of outermost on the inner annulus and innermost on the outer annulus is what gives this property.</p>
<p>For any previously exposed exterior $\xi$ outside $B_{l_i}$ admissible for $V$, this yields the common lower bound</p>
<div class="math-display">$$\mu_\eta(\Gamma_I=\gamma\mid V,\xi)\geq c_0\sum_{\gamma'}\mu_\eta(D(\gamma,\gamma')).$$</div>
<p>To verify it, write $g=\mu_\eta(V_{\operatorname{ext}\gamma'}\mid\xi)$. The denominator $\mu_\eta(V\mid\xi)$ is at most $g\,\mu_\eta^\gamma(B_s\leftrightarrow\gamma)$: every realization of $V$ has both properties, which depend on disjoint remaining regions. The numerator for $D(\gamma,\gamma')\cap V$ is at least</p>
<div class="math-display">$$\mu_\eta(D(\gamma,\gamma'))\,g\,\mu_\eta^\gamma(I_s\leftrightarrow\gamma).$$</div>
<p>Indeed, the seed path crosses to $\gamma'$, and the local-condition factorization then reconstructs $V$. All sites on the separating curves are already open in $D$; the interior probabilities are wired probabilities, so no boundary sites are counted twice. The seed comparison from the preceding gluing argument proves the bound. Zero terms may be omitted; the actual conditional denominator is positive.</p>
<p>The lower measure on nonempty $\gamma$ has total mass at least some $\kappa&gt;0$. Require a separator in each annulus and a crossing from inside the first to outside the second. RSW and Harris give a uniform positive probability for this event, and it forces $\Gamma_I$ and $\Gamma_O$ to be connected. The bound is the same for $W$ and every admissible exterior for $W$.</p>
<p>First sample the two exteriors outside $B_C$ with their correct conditional laws. At each stage couple the two conditional distributions of $\Gamma_I$ by putting their common mass on identical nonempty curves. This succeeds with probability at least $\kappa$, whatever has happened earlier. If the stage fails, expose the rest of that annulus with its correct conditional laws and continue. If it succeeds at $\gamma$, fill the two exteriors to $\gamma$ with their correct conditional laws and use a single common interior configuration with law</p>
<div class="math-display">$$\mu_\eta^\gamma(\,\cdot\mid V_{\operatorname{int}\gamma})
=\mu_\eta^\gamma(\,\cdot\mid W_{\operatorname{int}\gamma}).$$</div>
<p>The equality follows from comparability. The two point-version indicators then agree by the separator identity. Every sampling step uses a conditional distribution of the intended marginal, so the completed configurations have laws $\mu_\eta(\cdot\mid V)$ and $\mu_\eta(\cdot\mid W)$. If $S$ is the event of at least one success,</p>
<div class="math-display">$$\widetilde\mu(S^c)\leq(1-\kappa)^{N+1}=:\delta_s.$$</div>
<p>This alone is an additive estimate. Leave the core $B_{l_{N+1}}$ unrevealed until the end; its radius lies in $[4s,16s)$. Given the two configurations outside this core, either marginal core law is its original product law conditioned on its own local condition and exterior. This follows at each failed stage by fresh conditional sampling, and after success by restriction of the common interior law. The success event is determined before the core is sampled. For $A=S$ or $S^c$, applying R77Z and averaging gives joint point-event probabilities between $c_2a_\eta(2s)\widetilde\mu(A)$ and $C_2a_\eta(2s)\widetilde\mu(A)$ in either marginal. After a success, the remaining annuli are sampled identically before the common core is drawn; hence observing the other exterior adds no information about that core. A part of probability zero contributes zero.</p>
<p>Now apply <a href="/tag/KJWA/">the relative coupling estimate</a>. The relative error is at most $(C_2/c_2)\delta_s/(1-\delta_s)$. Finally, $N+1\geq\log_4(C/s)-2$ gives $\delta_s\leq(1-\kappa)^{-2}(s/C)^\beta$, where $\beta=-\log(1-\kappa)/\log4&gt;0$. This proves the assertion. At no point is Harris applied to $S$ or $S^c$.</p>

## Conformal radius and the real boundary {#section-conformal-radius}

<a id="tag-7GOV" data-assertion="proposition" data-title="The conformal-radius distance comparison includes every component of the domain boundary"></a>
<p>Let $D\subsetneq\mathbb C$ be simply connected, $w\in D$, and let $\rho_D(w)=1/|\phi'(w)|$ for a conformal map $\phi:D\to\mathbb D$ with $\phi(w)=0$. Then</p>
<div class="math-display">$$\rho_D(w)/4\leq\operatorname{dist}(w,\partial D)\leq\rho_D(w).$$</div>
<p>If $D$ is the simply connected component of $w$ in $\mathbb H\setminus A$, with $A$ closed relative to the half-plane, the middle quantity is</p>
<div class="math-display">$$\min\{\operatorname{Im}w,\operatorname{dist}(w,A)\}.$$</div>
<p>In particular, if $\rho_D(w)&lt;t&lt;\operatorname{Im}w$, then $\operatorname{dist}(w,A)&lt;t$; and $\operatorname{dist}(w,A)&lt;t/4$ always implies $\rho_D(w)&lt;t$.</p>
<p><em>Proof.</em> Koebe's quarter theorem applied to $\phi^{-1}$ places the disk of radius $\rho_D(w)/4$ inside $D$. Conversely, every disk about $w$ of radius less than the boundary distance lies in $D$; Schwarz's lemma applied to its inclusion gives that radius at most $\rho_D(w)$. The closest obstruction to staying in a component of $\mathbb H\setminus A$ is either $A$ or the real boundary, proving the minimum formula and the two implications.</p>
<p>The real boundary cannot be omitted. Take $A=\mathbb R+10i$ and $w=i$. The component is the strip $0&lt;\operatorname{Im}z&lt;10$, whose conformal radius at $i$ is $(20/\pi)\sin(\pi/10)&lt;2$, while $\operatorname{dist}(i,A)=9$. The source's inequality (2.2) would give the opposite comparison. For its fixed bulk point, choosing $t&lt;\operatorname{Im}w$ repairs the use of that inequality. See the <a href="/errata/conijn-factorization-2015/#real-boundary-distance">provisional erratum</a>. Simple connectivity is part of the definition used here; it does not follow for an arbitrary closed obstacle without an additional condition.</p>

## Removing the neighbourhoods {#section-point-lifting}

<p>Fix $x&lt;y$ on the real boundary and $w\in\mathbb H$. Choose $C$ so that the three $C$-boxes are disjoint, the bulk box lies in $\mathbb H$, and all remote marks lie outside each local box. For small $s_x,s_y,t$, put $J_x=[x,x+s_x]$, $J_y=[y-s_y,y+s_y]$. Let $\mathcal C(J)$ be the union of open clusters meeting $J$, and set</p>
<div class="math-display">$$E_{xy}=\{\mathcal C(J_x)\cap J_y\ne\varnothing\},\quad
E_{xw}=\{\rho(w,\mathcal C(J_x))&lt;t\},\quad
E_{yw}=\{\rho(w,\mathcal C(J_y))&lt;t\},\quad E_{xyw}=E_{xy}\cap E_{xw}.$$</div>
<p>Conformal radius uses the component left after deleting the boundary-attached cluster set, and is zero if it contains $w$. Such components are simply connected: adjoining the lower half-plane to all the attached clusters gives a connected complement. The two events in $E_{xyw}$ can initially involve different clusters meeting $J_x$.</p>
<p>A bullet in place of a neighbourhood means that the corresponding mark itself is reached. Removing neighbourhoods in the order $y,x,w$ gives nested events $E_{xyw}^{0}\supset E_{xyw}^{1}\supset E_{xyw}^{2}\supset E_{xyw}^{3}$: first require $y\in\mathcal C(J_x)$, then $x\leftrightarrow y$ and $\rho(w,\mathcal C(x))&lt;t$, then $x,y,w$ in one cluster. For each pair use the same order restricted to its two marks.</p>

<a id="tag-IP6C" data-assertion="theorem" data-title="Uniform point completion transfers the continuum neighbourhood factorization to the discrete three-point ratio"></a>
<p>Assume critical-site RSW and the following continuum input. For fixed positive neighbourhood radii the four event probabilities have positive limits $f_{xy},f_{xw},f_{yw},f_{xyw}$ as $\eta\downarrow0$; for every $\varepsilon,s_0&gt;0$ there are $s_x,s_y,t\in(0,s_0)$ for which</p>
<div class="math-display">$$\left|\frac{f_{xyw}^2}{f_{xy}f_{xw}f_{yw}}-K_F\right|&lt;\varepsilon.$$</div>
<p>Then the discrete three-point squared ratio tends to $K_F=128\pi^5/(3^{3/2}\Gamma(1/3)^9)$. The continuum input is Conijn's Theorem 3, obtained from Beliaev–Izyurov; the implication proved here supplies the neighbourhood-to-site step of JM5A.</p>
<p><em>Proof.</em> The events just defined satisfy 83WA at every mark whose neighbourhood remains. At a boundary mark the projection to its $C$-box says that its small interval connects to the wired box boundary. At the bulk mark it says that the cluster attached to the wired box boundary has conformal radius less than $t$. These descriptions do not depend on which remote connections have already been required. To see this, open every site outside the box in the definition of the projection. Conversely every path from a local neighbourhood to a remote mark must leave the box. For the bulk event, use 7GOV with $t&lt;\operatorname{Im}w$ to obtain a cluster point inside the small box.</p>
<p>On an open separator, any local-to-remote path first hits that separator. Wiring it makes the clusters visible from the exterior independent of the interior configuration, and conversely makes the cluster visible from the interior depend only on the wired separator. This gives the projection factorization, including for the intersection $E_{xyw}$. The seed segment lies in the boundary interval. At the bulk mark, connection from a segment of length $t/8$ to the separator places its cluster within $t/8$ of $w$, so 7GOV makes the conformal radius less than $t$. Replacing a neighbourhood by its mark has exactly the point-version property. Thus all conditions compared at a given mark are comparable, even if the two remote demands were carried by different clusters before the separator was opened. These observations also handle the intermediate events with bullets.</p>
<p>Let $a_i$ be the three conditional probabilities of the successive point completions for the triple. Each pair probability has two such factors, denoted $b_{ij,i}$ and $b_{ij,j}$. The chain rule gives the exact identity</p>
<div class="math-display">$$\frac{\mu_\eta(x\leftrightarrow y\leftrightarrow w)^2}
{\mu_\eta(x\leftrightarrow y)\mu_\eta(x\leftrightarrow w)\mu_\eta(y\leftrightarrow w)}
=\frac{\mu_\eta(E_{xyw})^2}{\mu_\eta(E_{xy})\mu_\eta(E_{xw})\mu_\eta(E_{yw})}
\prod_{i\in\{x,y,w\}}\prod_{j\ne i}\frac{a_i}{b_{ij,i}}.$$</div>
<p>Each of the six quotients lies between $1-\varepsilon_0$ and $1+\varepsilon_0$ once the three radii are sufficiently small and then the mesh is sufficiently fine, by XP8A. This estimate is uniform over all smaller mesh sizes. Choose such a radius bound first, and use the continuum input to choose one triple of positive radii below it with continuum ratio close to $K_F$. Keep these radii fixed while taking $\eta\downarrow0$. The liminf and limsup of the discrete ratio are trapped between $(K_F-\varepsilon)(1-\varepsilon_0)^6$ and $(K_F+\varepsilon)(1+\varepsilon_0)^6$. Let both errors tend to zero. Only the existence of sufficiently small good radii was used; no joint limit or interchange of neighbourhood and mesh limits was assumed.</p>

## An interval remains on the boundary {#section-interval-limit}

<a id="tag-7O0U" data-assertion="theorem" data-title="The boundary-interval attachment ratio has an explicit strip-coordinate limit"></a>
<p>Fix $a&lt;b&lt;c$ on the real line and $w\in\mathbb H$, and let $J=[a,b]$. Under the critical triangular-site law,</p>
<div class="math-display">$$\lim_{\eta\downarrow0}\frac{\mu_\eta(c,w\in\mathcal C(J))}{\mu_\eta(c\in\mathcal C(J))\mu_\eta(w\in\mathcal C(J))}
=\frac{e^{\pi X/3}H(X)}{H(0)},\quad
H(X)={}_2F_1(-1/2,-1/3;7/6;e^{-2\pi X}),$$</div>
<p>where $X=\operatorname{Re}\Psi(w)$ and $\Psi$ maps $(\mathbb H;a,b,c)$ to the half-strip $(\{X&gt;0,0&lt;Y&lt;1\};i,0,\infty)$. The numerator allows $c$ and $w$ to lie in different clusters that each meet $J$; it does not require them to be connected to each other.</p>
<p><em>Proof from the continuum inputs.</em> Keep $J$ fixed. Replace $c$ by a short boundary interval of radius $s$ and the demand at $w$ by a conformal-radius neighbourhood of size $t$. Let $E_{cw}$ be the intersection of these two attachment events, with marginals $E_c,E_w$. The source continuum formulas, stated as Theorem 4 and Lemma 5 in Conijn, give</p>
<div class="math-display">$$\lim_{t\downarrow0}\lim_{s\downarrow0}\lim_{\eta\downarrow0}
\frac{\mu_\eta(E_{cw})}{\mu_\eta(E_c)\mu_\eta(E_w)}
=\frac{\pi^{5/48}|\Psi'(w)|^{5/48}G(X,Y)}{2^{5/48}H(0)|\phi'(w)|^{5/48}(\sin(\pi\omega/2))^{1/3}},$$</div>
<p>where $\phi:\mathbb H\to\mathbb D$ sends $w$ to zero, $\omega$ is the harmonic measure of $J$ seen from $w$, and</p>
<div class="math-display">$$G(X,Y)=e^{\pi X/3}H(X)\sinh(\pi X)^{-1/3}
\left(\frac{\sinh^2(\pi X)\sin^2(\pi Y)}{\sinh^2(\pi X)+\sin^2(\pi Y)}\right)^{11/96}.$$</div>
<p>These continuum identities and critical-site RSW are external inputs; their SLE derivation is not proved here. Choose the two local boxes away from $J$ and each other, with the bulk box strictly inside the half-plane. The same projection argument as IP6C applies. Completing first the boundary mark and then the bulk mark expresses the desired lattice ratio as the neighbourhood ratio times two conditional-completion quotients. Each tends uniformly to one by XP8A. Choose $t$, then $s$, then let the mesh tend to zero, keeping the completion errors uniformly small. The same liminf/limsup argument transfers the displayed iterated limit to the site ratio. The remaining algebra is V456 below. This is Conijn's Theorem 2 with the attachment event and order of limits retained.</p>

<a id="tag-V456" data-assertion="proposition" data-title="The conformal derivative and harmonic-measure factors cancel in the strip attachment formula"></a>
<p>For the maps and functions just defined, the continuum quotient in the preceding display equals $e^{\pi X/3}H(X)/H(0)$.</p>
<p><em>Proof.</em> Let $\Pi$ be the real Möbius map taking $a,b,c$ to $-1,1,\infty$, put $z=\Pi(w)$, and choose the branch $\arcsin z=u+iv$ with $-\pi/2&lt;u&lt;\pi/2$ and $v&gt;0$. Then $\Psi(w)=v/\pi+i(1/2-u/\pi)$. Write $S=\sinh v$, $T=\cos u$, and $Q=|1-z^2|$. Since $z=\sin(u+iv)$,</p>
<div class="math-display">$$\operatorname{Im}z=ST,\qquad Q=S^2+T^2,\qquad
|\phi'(w)|=\frac{|\Pi'(w)|}{2ST},\qquad
|\Psi'(w)|=\frac{|\Pi'(w)|}{\pi\sqrt Q}.$$</div>
<p>Both $S,T$ are positive. Substituting into the quotient cancels $|\Pi'|$, all powers of $\pi$ and $2$, and leaves</p>
<div class="math-display">$$\frac{e^{\pi X/3}H(X)}{H(0)}
\left(\frac{T}{\sqrt Q\sin(\pi\omega/2)}\right)^{1/3}.$$</div>
<p>The angle subtended by $[-1,1]$ at $z$ is $\pi\omega$. Its cosine is $(|z|^2-1)/Q$, while $|z|^2=\sin^2u+\sinh^2v=1-T^2+S^2$. The half-angle identity therefore gives $\sin^2(\pi\omega/2)=T^2/Q$. Positivity removes any sign ambiguity and the last factor is one.</p>

<a id="tag-ZZ9Q" data-assertion="proposition" data-title="The strip factorization ratio increases from one and has an explicit large-distance equivalent"></a>
<p>The function $\psi(X)=e^{\pi X/3}H(X)/H(0)$ is strictly increasing for $X&gt;0$, tends to one as $X\downarrow0$, and satisfies $\psi(X)\sim e^{\pi X/3}/H(0)$ as $X\to\infty$.</p>
<p><em>Proof.</em> Put $F(q)={}_2F_1(-1/2,-1/3;7/6;q)$. Its power-series coefficients $c_n=(-1/2)_n(-1/3)_n/((7/6)_n n!)$ are positive, including $c_0=1$. For $0&lt;q&lt;1$, the logarithmic derivative $m(q)=qF'(q)/F(q)$ is the mean of $n$ under weights $c_nq^n/F(q)$. Differentiating with respect to $\log q$ gives its strictly positive variance, so $m$ increases. Gauss summation and the derivative identity for the hypergeometric series give $F'(1)=F(1)/6$, with finite values. Thus $m(q)&lt;1/6$ for $q&lt;1$. Since $q=e^{-2\pi X}$,</p>
<div class="math-display">$$\frac{d}{dX}\log\psi(X)=\pi/3-2\pi m(e^{-2\pi X})&gt;0.$$</div>
<p>Continuity at $q=1$ gives the first limit, and $F(0)=1$ gives the second. In particular $\psi(X)&gt;1$, as is consistent with Harris association for the two interval-attachment events. This is a consequence of the explicit formula, not a new percolation scaling input.</p>


<p>The bulk-boundary density input now has a <a href="/articles/continuum-connection-densities/#section-jacobi-spectrum">complete angular spectral calculation</a>, including the coefficient $18/(5\pi)$ and a uniform relative error. Its identification with the percolation observable remains an explicit radial-SLE input. The five-point continuum formula still needs the terminal SLE argument recorded there; the lattice passage above is unchanged.</p>


<p>The later <a href="/articles/continuum-connection-densities/#section-terminal-formula">terminal continuation</a> supplies the five-point candidate calculation and optional stopping, with the terminal percolation identification and foundational SLE results retained as explicit inputs. Its integrability bound is proved under the conditioned law. It therefore resolves the analytic obligations described above without claiming the remaining exploration inputs or changing the lattice passage.</p>
