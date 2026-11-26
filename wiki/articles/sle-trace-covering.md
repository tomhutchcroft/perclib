---
{
  "id": "sle-trace-covering",
  "title": "Covering the SLE trace",
  "subtitle": "From conformal radius to small-ball probabilities and Hausdorff upper bounds",
  "kind": "method",
  "category": "General theory",
  "summary": "A deterministic trace argument identifies the terminal domain-boundary distance. Uniform small-ball bounds then give the expected covering exponent and the Hausdorff upper bound, with localization handled by separate inner and outer grids.",
  "context": [
    "We assume the ordinary chordal Loewner chain has a continuous generating trace: its domains are the unbounded components of the complements of the past trace, and the trace is given by boundary limits of inverse Loewner maps.",
    "This trace-generation theorem is a named input, not proved here. Rohde–Schramm Theorem 5.1 supplies it away from kappa8; their cited Lawler–Schramm–Werner extension supplies the kappa8 case.",
    "The moment and tail estimates used below are proved in the conformal-radius article. The dimension statements concern ordinary SLE with kappa greater than zero, without force points or conditioning.",
    "An expected covering exponent and a Hausdorff upper bound do not establish a Hausdorff lower bound."
  ],
  "related": ["sle-conformal-radius", "sle-swallowing", "continuum-connection-densities"],
  "sourceIds": ["rohde-schramm-basic-sle-2005"],
  "aliases": ["SLE covering dimension", "SLE small-ball probabilities", "SLE Hausdorff upper bound"],
  "prototypeUses": []
}
---

## The distance after swallowing {#section-trace-distance}

<p>Let $\gamma:[0,\infty)\to\overline{\mathbb H}$ be a continuous generating trace of a chordal Loewner chain, and write $\Gamma=\gamma[0,\infty)$. Thus $D_t$ is the unbounded component of $\mathbb H\setminus\gamma[0,t]$, and $D_t=\{z:\tau(z)>t\}$. Assume the inverse-map boundary limit defining $\gamma(t)$ exists at every time.</p>

<a id="tag-G0UQ" data-assertion="proposition" data-title="The terminal domain-boundary distance equals distance to the full generating trace and the real line"></a>
<p>For every $z=x+iy\in\mathbb H$,</p>
<div class="math-display">$$\lim_{t\uparrow\tau(z)}\operatorname{dist}(z,\partial D_t)
=\operatorname{dist}(z,\Gamma\cup\mathbb R)
=\min\{y,\operatorname{dist}(z,\Gamma)\}.$$</div>
<p>This identity does not require transience of the trace.</p>
<p><em>Proof.</em> For $t<\tau(z)$, a disk centered at $z$ avoids $\gamma[0,t]\cup\mathbb R$ if and only if it lies in $D_t$: a disk avoiding that closed set stays in the component containing $z$, and $D_t$ is disjoint from the set. Hence</p>
<div class="math-display">$$\operatorname{dist}(z,\partial D_t)
=\operatorname{dist}(z,\gamma[0,t]\cup\mathbb R).$$</div>
<p>If $\tau(z)=\infty$, taking the infimum over $t$ proves the claim. Suppose instead that $\tau(z)<\infty$. Continuity of $\gamma$ on this finite interval shows that the limit of the last display is</p>
<div class="math-display">$$r=\operatorname{dist}(z,\gamma[0,\tau(z)]\cup\mathbb R).$$</div>
<p>There is nothing to prove if $r=0$. If $r>0$, the disk $B(z,r)$ lies in one component of $\mathbb H\setminus\gamma[0,\tau(z)]$. Since $z\notin D_{\tau(z)}$, that component is not the unbounded component. In particular $B(z,r)$ is disjoint from $\overline{D_{\tau(z)}}$.</p>
<p>For every $s\geq t$, the inverse-map definition places $\gamma(s)$ in $\overline{D_s}\subseteq\overline{D_t}$. Taking $t=\tau(z)$ shows that the future trace cannot enter $B(z,r)$. Its distance from $z$ therefore cannot improve on the distance already attained by the past trace and the real line. This proves the first equality; the second is the distance formula for a union.</p>

## Uniform small-ball bounds {#section-uniform-hitting}

<p>Assume ordinary chordal $\operatorname{SLE}_\kappa$ has the continuous generating trace just specified. For $0<\kappa<8$, put $\lambda=1-\kappa/8$.</p>

<a id="tag-VEZ7" data-assertion="proposition" data-title="SLE small-ball probabilities have uniform power bounds on compact subsets of the half-plane"></a>
<p>For every nonempty compact $K\subset\mathbb H$ and every $p\in(0,\lambda)$, there are positive constants $c,C_p,\varepsilon_0$ such that</p>
<div class="math-display">$$c\varepsilon^\lambda
\leq\mathbb P\bigl(\operatorname{dist}(z,\Gamma)<\varepsilon\bigr)
\leq C_p\varepsilon^p
\qquad(z\in K,\ 0<\varepsilon<\varepsilon_0).$$</div>
<p>For $\kappa\geq8$, under the same trace hypothesis, $\operatorname{dist}(z,\Gamma)=0$ almost surely for each fixed $z\in\mathbb H$.</p>
<p><em>Proof.</em> Take $\varepsilon_0<\frac12\inf_{z\in K}\operatorname{Im}z$. By G0UQ, the event in question is exactly the terminal domain-distance event in <a href="/articles/sle-conformal-radius/#section-distance-exponent">DC8Q</a>. For $z=x+iy$ and $\theta=\arg z$, that result gives</p>
<div class="math-display">$$
\sin^{8/\kappa-1}\theta\left(\frac{\varepsilon}{2y}\right)^\lambda
\leq\mathbb P\bigl(\operatorname{dist}(z,\Gamma)<\varepsilon\bigr)
\leq\mathbb E[\mathcal Z(z)^p]\left(\frac{2\varepsilon}{y}\right)^p.
$$</div>
<p>On $K$, $y$ is bounded above and away from zero, and $\sin\theta$ is bounded away from zero. Moreover, the positive-integral proof of <a href="/articles/sle-conformal-radius/#section-exact-moments">K0WT</a> gives $\mathbb E[\mathcal Z(z)^p]\leq1/F_p(1)$, with $F_p(1)>0$ independent of $z$. These facts make both bounds uniform. For $\kappa\geq8$, DC8Q gives zero terminal domain distance, and G0UQ identifies it with distance to $\Gamma$, since $z$ has positive height.</p>

## Expected covering numbers {#section-expected-covering}

<p>For a bounded set $F\subset\mathbb C$, let $N(\varepsilon,F)$ be the least number of open disks of radius $\varepsilon$ needed to cover $F$, with $N(\varepsilon,\varnothing)=0$.</p>

<a id="tag-1424" data-assertion="theorem" data-title="The expected SLE trace covering exponent is one plus kappa over eight, capped at two"></a>
<p>Under the trace hypothesis above, let $A$ be a nonempty bounded open set with $\overline A\subset\mathbb H$. For $0<\kappa<8$ and every $p\in(0,1-\kappa/8)$,</p>
<div class="math-display">$$
c_A\varepsilon^{-(1+\kappa/8)}
\leq \mathbb E[N(\varepsilon,\Gamma\cap A)]
\leq C_{A,p}\varepsilon^{-(2-p)}
$$</div>
<p>for all sufficiently small $\varepsilon>0$. Constants may depend on $A$ and $\kappa$, and the upper constant also on $p$. For $\kappa\geq8$, the expectation is bounded above and below by positive multiples of $\varepsilon^{-2}$. In particular, for every $\kappa>0$,</p>
<div class="math-display">$$
\lim_{\varepsilon\downarrow0}
\frac{\log\mathbb E[N(\varepsilon,\Gamma\cap A)]}{|\log\varepsilon|}
=\min\{1+\kappa/8,2\}.
$$</div>
<p><em>Proof.</em> For the upper bound, use the grid $\varepsilon\mathbb Z^2$ and retain its points $z_j$ at distance less than $\varepsilon$ from $A$. There are at most $C_A\varepsilon^{-2}$ such points, all in a fixed compact subset of $\mathbb H$ when $\varepsilon$ is small. Every point of $\Gamma\cap A$ lies within $\varepsilon/\sqrt2$ of one of these grid points. Thus disks of radius $\varepsilon$ centered at the retained points satisfying $\operatorname{dist}(z_j,\Gamma)<\varepsilon$ cover $\Gamma\cap A$, and</p>
<div class="math-display">$$
\mathbb E[N(\varepsilon,\Gamma\cap A)]
\leq\sum_j\mathbb P\bigl(\operatorname{dist}(z_j,\Gamma)<\varepsilon\bigr)
\leq C_{A,p}\varepsilon^{p-2}.
$$</div>
<p>For the lower bound, choose a disk $B(z_0,2r)$ whose closure lies in $A$. Use grid points $z_j\in5\varepsilon\mathbb Z^2\cap B(z_0,r)$. There are at least $c_A\varepsilon^{-2}$ of them for small $\varepsilon$. Whenever $\operatorname{dist}(z_j,\Gamma)<\varepsilon$, a witnessing trace point lies in $A$. In any cover of $\Gamma\cap A$ by $\varepsilon$-disks, such a witness belongs to a covering disk whose center is within $2\varepsilon$ of $z_j$.</p>
<p>No one covering disk can account for two of these grid points: their separation is at least $5\varepsilon$, whereas two points within $2\varepsilon$ of its center are at distance less than $4\varepsilon$. Consequently, pathwise,</p>
<div class="math-display">$$
\#\{j:\operatorname{dist}(z_j,\Gamma)<\varepsilon\}
\leq N(\varepsilon,\Gamma\cap A).
$$</div>
<p>Taking expectations and applying VEZ7 gives the lower bound $c_A\varepsilon^{\lambda-2}$. These two estimates imply that the lower logarithmic limit is at least $2-\lambda$, while the upper limit is at most $2-p$ for every $p<\lambda$. Letting $p\uparrow\lambda$ proves the displayed limit for $\kappa<8$.</p>
<p>For $\kappa\geq8$, every fixed grid point has zero distance to $\Gamma$ almost surely by VEZ7. The inner-grid argument gives the lower bound $c_A\varepsilon^{-2}$. The deterministic grid cover of $A$ gives the matching upper bound. This argument needs density near the finitely many grid points, not transience or a claim that the entire half-plane has already been visited.</p>
<p>Rohde–Schramm state a logarithmic limsup in Theorem 8.1. The lower-tail estimate already proved in DC8Q gives a lower bound at every sufficiently small scale, so the argument here yields the full logarithmic limit. It does not identify a leading constant.</p>

## The Hausdorff upper bound {#section-hausdorff-upper}

<a id="tag-YBRV" data-assertion="corollary" data-title="The Hausdorff dimension of an ordinary SLE trace is at most one plus kappa over eight below kappa eight"></a>
<p>For $0<\kappa<8$, under the same continuous-trace hypothesis,</p>
<div class="math-display">$$\dim_{\mathrm H}\Gamma\leq1+\kappa/8\qquad\text{almost surely}.$$</div>
<p><em>Proof.</em> Fix $q>1+\kappa/8$ and a bounded open $A$ with closure in $\mathbb H$. Choose $p$ with $0<p<1-\kappa/8$ and $q+p-2>0$. For $\varepsilon_n=2^{-n}$, the upper bound in 1424 gives</p>
<div class="math-display">$$
\sum_n\mathbb E\!\left[(2\varepsilon_n)^q
N(\varepsilon_n,\Gamma\cap A)\right]
\leq C\sum_n2^{-n(q+p-2)}<\infty.
$$</div>
<p>By Tonelli, the random series is finite almost surely, so its terms tend to zero. The corresponding disk covers have diameters at most $2\varepsilon_n\downarrow0$ and total $q$-cost tending to zero. Hence the $q$-dimensional Hausdorff measure of $\Gamma\cap A$ is zero.</p>
<p>Take a countable exhaustion of $\mathbb H$ by such sets $A$, and then a countable sequence of $q$ decreasing to $1+\kappa/8$. The result follows for $\Gamma\cap\mathbb H$. The remainder lies on $\mathbb R$ and has dimension at most one. This proves the upper bound for the whole trace. No Hausdorff lower bound follows from the expected covering count alone.</p>

## Localizing the grid comparison {#section-grid-localization}

<p>The proof of <a href="https://arxiv.org/html/math/0106036v4">Rohde–Schramm, Theorem 8.1</a> counts grid points within $\varepsilon$ of $A$ and the full trace, then bounds that count by $100N(\varepsilon,\Gamma\cap A)$. As a deterministic comparison, the latter inequality can fail when the trace comes near $A$ from outside it.</p>
<p>For example, take the vertical trace $\Gamma=i[0,\infty)$, $A=B(0.04+i,0.01)$ and $\varepsilon=0.1$. Then $\Gamma\cap A$ is empty, so its covering number is zero. But the grid point $i\in\varepsilon\mathbb Z^2$ is within $\varepsilon$ of $A$ and lies on the trace, so the counted set is nonempty. Also $\varepsilon<\operatorname{dist}(A,\mathbb R)$, as the source requires.</p>
<p>The proof of 1424 uses the outer grid only for the upper bound, and a separated grid strictly inside $A$ for the lower bound. This repairs the localization step without changing the source theorem. The <a href="/errata/rohde-schramm-basic-sle-2005/#covering-grid-localization">erratum remains provisional</a>. The example diagnoses the geometric comparison; it is not a counterexample to the dimension theorem for positive $\kappa$.</p>



## The trace input away from eight {#section-generation-update}

<p>The continuous generating trace and full inverse-map boundary limits assumed above are now supplied for ordinary SLE with kappa different from eight by <a href="/tag/MN2A/">MN2A</a>. This uses the written derivative and joint radial-continuity proofs followed by the deterministic criterion <a href="/tag/N2VO/">N2VO</a>. The kappa-eight case retains the separate Lawler–Schramm–Werner input identified above. The covering estimates and their hypotheses have not been changed.</p>


## Hull boundaries below kappa eight {#section-hull-boundaries}

<p>Write $K_t=\overline{\mathbb H\setminus D_t}$, with closure in $\mathbb C$, and $\Gamma=\gamma[0,\infty)$. The boundary of a filled hull can be much smaller than the trace, but it cannot acquire new interior boundary points away from the past trace.</p>

<a id="tag-NHWR" data-assertion="corollary" data-title="Below kappa eight all finite-time SLE hull boundaries have dimension at most one plus kappa over eight"></a>
<p>For $0\leq\kappa&lt;8$, almost surely, simultaneously for every $t&gt;0$,</p>
<div class="math-display">$$\partial K_t\subseteq\gamma[0,t]\cup\mathbb R,\qquad
\dim_{\mathrm H}\partial K_t\leq1+\frac\kappa8&lt;2.$$</div>
<p>On the same event the full trace and every finite-time hull boundary have zero planar Lebesgue area. The boundary-area conclusion also holds at time zero, when $K_0=\varnothing$.</p>

<p><em>Proof.</em> First consider any continuous generating trace and fix $t$. If $z\in\mathbb H\setminus\gamma[0,t]$, a small open disk about $z$ misses the past trace and the real line. This disk lies in a single component of $\mathbb H\setminus\gamma[0,t]$. If it meets the unbounded component $D_t$, the whole disk lies in $D_t$. Consequently</p>
<div class="math-display">$$\partial D_t\cap\mathbb H\subseteq\gamma[0,t].$$</div>
<p>Inside $\mathbb H$, the hull is the complement of $D_t$, so $\partial K_t\cap\mathbb H\subseteq\partial D_t$. Outside $\mathbb H$, the hull has points only on the real line. This proves the displayed containment, pathwise at every time.</p>

<p>For $0&lt;\kappa&lt;8$, combine this containment with the single probability-one event of YBRV, on which $\dim_{\mathrm H}\Gamma\leq1+\kappa/8$. The dimension of a union of two sets is the maximum of their dimensions, and the real line has dimension one. This gives the boundary bound for all $t$ together; no intersection over times is needed. A set of Hausdorff dimension strictly less than two has zero planar area, proving both area conclusions. When $\kappa=0$, the full trace is the vertical half-line and each positive-time hull is a vertical segment, so the assertions follow directly.</p>

<p>This argument includes $\kappa=4$. It uses the trace dimension estimate, not the fixed-time Holder extension theorem, which excludes that parameter. It supplies a simultaneous boundary-dimension bound below eight without the separate theorem about boundaries of Holder domains used in Rohde–Schramm Corollary 5.3. No optimality is asserted for the hull-boundary exponent. At and above eight, the zero-area boundary input in the space-filling argument still requires a different proof.</p>
