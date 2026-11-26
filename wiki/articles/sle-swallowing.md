---
{
  "id": "sle-swallowing",
  "title": "SLE swallowing times",
  "subtitle": "Finite physical lifetime and a beta law for boundary intervals",
  "kind": "method",
  "category": "General theory",
  "summary": "Two harmonic martingales prove finite Loewner lifetime above kappa four. A ratio of boundary flows gives the probability of simultaneous swallowing; a separate geometric input identifies the trace hitting law.",
  "context": [
    "These arguments concern ordinary chordal SLE in the upper half-plane, without force points or conditioning.",
    "Standard Loewner theory, local uniqueness for stochastic differential equations, Itô calculus, Brownian time change and bounded-martingale convergence are foundational inputs.",
    "Finite lifetime means that a point enters the Loewner hull. It does not by itself distinguish a point on the trace from a point cut off by the trace. The geometric input for the boundary hitting law is stated separately."
  ],
  "related": ["sle-conformal-radius", "continuum-connection-densities"],
  "sourceIds": ["rohde-schramm-basic-sle-2005"],
  "aliases": ["SLE physical lifetime", "simultaneous swallowing", "SLE boundary hitting distribution"],
  "prototypeUses": []
}
---

## Time spent inside a disk {#section-bounded-exit}

<p>Let $U_t=\sqrt\kappa B_t$ and $Z_t=g_t(z)-U_t$, where $g_t$ is the chordal Loewner flow. For a fixed $z\in\overline{\mathbb H}\setminus\{0\}$, let $\tau(z)$ be the maximal lifetime before the flow reaches its singularity. Thus</p>
<div class="math-display">$$dZ_t=\frac2{Z_t}\,dt-\sqrt\kappa\,dB_t,\qquad Z_0=z.$$</div>
<p>For an interior point this is the same lifetime as in the <a href="/articles/sle-conformal-radius/#section-radius-clock">conformal-radius argument</a>, but the time parameter here is the original Loewner time.</p>

<a id="tag-JCIS" data-assertion="proposition" data-title="The Loewner flow exits a bounded half-disk or reaches its singularity in integrable time"></a>
<p>Suppose $\kappa&gt;4$. Put $b=1-4/\kappa$ and $\phi=\pi(1-b)/2$. For $R&gt;|z|$, stop at the first time $|Z_t|=R$ or at $\tau(z)$, whichever comes first, and call this time $T_R$. Then</p>
<div class="math-display">$$\mathbb E[T_R]\leq\frac{R^2}{\kappa b^2\cos^2\phi}.$$</div>
<p><em>Proof.</em> Use the branch $0\leq\arg w\leq\pi$ and set</p>
<div class="math-display">$$F(w)=e^{i\phi}w^b,\qquad f(w)=\operatorname{Re}F(w),\qquad h(w)=\operatorname{Im}F(w).$$</div>
<p>The drift in Itô's formula for $F(Z_t)$ vanishes, since</p>
<div class="math-display">$$\frac2wF'(w)+\frac\kappa2F''(w)
=be^{i\phi}w^{b-2}\left(2+\frac\kappa2(b-1)\right)=0.$$</div>
<p>Both real and imaginary parts are local martingales. The useful lower bound comes from the real part:</p>
<div class="math-display">$$\partial_xf(w)=b|w|^{b-1}\cos\bigl(\phi+(b-1)\arg w\bigr)
\geq b\cos\phi\,R^{b-1},\qquad 0&lt;|w|\leq R.$$</div>
<p>Indeed, the angle in this cosine lies in $[-\phi,\phi]$, and $0&lt;\phi&lt;\pi/2$. Stop first when $|Z|$ leaves $(\delta,R)$, with $0&lt;\delta&lt;|z|$, and denote this time by $T_{\delta,R}$. All derivatives are bounded on the stopped half-annulus. For real starting points the upper branch extends locally across the real axis away from zero, so the same calculation applies. The martingale $M_t=f(Z_{t\wedge T_{\delta,R}})$ is bounded by $R^b$ in absolute value. For each deterministic $n$, the second-moment identity gives</p>
<div class="math-display">$$\kappa b^2\cos^2\phi\,R^{2b-2}\,
\mathbb E[T_{\delta,R}\wedge n]
\leq\mathbb E[\langle M\rangle_n]
=\mathbb E[M_n^2]-f(z)^2\leq R^{2b}.$$</div>
<p>Let $n\to\infty$ and then $\delta\downarrow0$. The exit times increase to a finite time $T$, with the asserted expectation bound. If the outer circle has not been reached, the values of $F(Z)$ along the inner exit times tend to zero. Bounded-martingale convergence for $f(Z)$ and $h(Z)$ before $T$ then gives $F(Z_t)\to0$, hence $Z_t\to0$. Away from zero the solution could be continued; there is no other finite endpoint in the bounded half-disk. Thus $T=T_R$, proving the bound.</p>

## Finite physical lifetime {#section-finite-lifetime}

<a id="tag-6DV8" data-assertion="theorem" data-title="Every fixed nonzero point of the closed half-plane has finite Loewner lifetime when kappa exceeds four"></a>
<p>For $\kappa&gt;4$ and each fixed $z\in\overline{\mathbb H}\setminus\{0\}$,</p>
<div class="math-display">$$\mathbb P\bigl(\tau(z)&lt;\infty\bigr)=1.$$</div>
<p><em>Proof.</em> The imaginary part used above satisfies</p>
<div class="math-display">$$h(w)=|w|^b\sin(\phi+b\arg w)\geq\sin\phi\,|w|^b.$$</div>
<p>It is positive throughout the closed half-plane except at zero. Stop at $T_R$, which is finite by JCIS. Bounded stopping on half-annuli and bounded convergence give $\mathbb E[h(Z_{T_R})]=h(z)$, taking the value zero at the singularity. Therefore</p>
<div class="math-display">$$\mathbb P\bigl(|Z_{T_R}|=R\bigr)
\leq\frac{h(z)}{\sin\phi\,R^b}.$$</div>
<p>On $\{\tau(z)=\infty\}$ the finite stopping time $T_R$ must be an exit through the outer circle. Letting $R\to\infty$ proves the claim.</p>
<p>This proves the fixed-point assertion in Rohde–Schramm Lemma 6.5. It does not exchange the quantifiers: a simultaneous assertion for every point requires an additional argument. Nor does it identify whether the point is hit or swallowed off the trace. For $4&lt;\kappa&lt;8$, finite physical lifetime coexists with the positive limiting conformal radius proved in K0WT.</p>

## The probability of simultaneous swallowing {#section-co-swallowing}

<p>Take $0&lt;u&lt;v$ on the real line. Until $\tau(u)$, write $x_t=g_t(u)-U_t$, $y_t=g_t(v)-U_t$ and $r_t=x_t/y_t$. The flow preserves $0&lt;x_t&lt;y_t$, so $\tau(u)\leq\tau(v)$.</p>

<a id="tag-KQIN" data-assertion="theorem" data-title="The probability that two positive boundary points have the same swallowing time is an incomplete beta function"></a>
<p>Suppose $4&lt;\kappa&lt;8$, and set</p>
<div class="math-display">$$a=1-\frac4\kappa,\qquad c=\frac8\kappa-1,\qquad
I_r(a,c)=\frac1{B(a,c)}\int_0^r q^{a-1}(1-q)^{c-1}\,dq.$$</div>
<p>Both beta parameters are positive. Almost surely the limit of $r_t$ as $t\uparrow\tau(u)$ is zero or one, and</p>
<div class="math-display">$$\{r_{\tau(u)-}=0\}=\{\tau(u)&lt;\tau(v)\},\qquad
\{r_{\tau(u)-}=1\}=\{\tau(u)=\tau(v)\}$$</div>
<p>up to null events. Consequently</p>
<div class="math-display">$$\mathbb P\bigl(\tau(u)=\tau(v)\bigr)=I_{u/v}(a,c).$$</div>
<p><em>Proof.</em> Introduce the clock $\sigma(t)=\int_0^t y_s^{-2}\,ds$. With the same Brownian motion in the two equations, Itô's formula gives</p>
<div class="math-display">$$dr_\sigma=\sqrt\kappa(r_\sigma-1)\,dW_\sigma
+(1-r_\sigma)\left(\frac2{r_\sigma}+2-\kappa\right)d\sigma,
\qquad d\log y_\sigma=\left(2-\frac\kappa2\right)d\sigma-\sqrt\kappa\,dW_\sigma.$$</div>
<p>The ratio generator is</p>
<div class="math-display">$$\mathcal L=\frac\kappa2(1-r)^2\frac{d^2}{dr^2}
+(1-r)\left(\frac2r+2-\kappa\right)\frac d{dr}.$$</div>
<p>For $f(r)=I_r(a,c)$ one has $f'(r)=r^{-4/\kappa}(1-r)^{8/\kappa-2}/B(a,c)$ and $\mathcal Lf=0$. Thus $f(r)$ is a bounded martingale. It converges, and since $f$ is a continuous strictly increasing bijection of $[0,1]$, the ratio has a limit $L\in[0,1]$.</p>
<p>Write $\Sigma=\lim_{t\uparrow\tau(u)}\sigma(t)$. The physical lifetime is finite by 6DV8. If $\Sigma&lt;\infty$, the equation for $\log y$ gives a positive finite limit for $y$. Maximality of the solution for $x$ forces $x\to0$, so $L=0$ and $\tau(u)&lt;\tau(v)$. If $\Sigma=\infty$, an interior limit $L$ is impossible: the quadratic-variation rate $\kappa(1-r)^2f'(r)^2$ would remain bounded below, whereas a bounded martingale has finite total quadratic variation almost surely.</p>
<p>It remains to rule out $L=0$ at infinite clock time. Choose $0&lt;q&lt;1-4/\kappa$. A direct calculation gives</p>
<div class="math-display">$$\mathcal L(r^q)=q(1-r)r^{q-2}
\left[\frac\kappa2(q-1)(1-r)+2+(2-\kappa)r\right].$$</div>
<p>The bracket is strictly negative near zero. There are therefore $\varepsilon,d&gt;0$ such that $\mathcal L(r^q)\leq-d$ on $(0,\varepsilon)$. Stopping on $(\delta,\varepsilon)$ and applying Itô's formula shows that the expected exit time is at most $r^q/d$, uniformly in $\delta$. Letting $\delta\downarrow0$ proves that a ratio starting in this interval must hit zero or return to $\varepsilon$ in finite clock time. By the Markov property at rational clock times, it cannot converge to zero while surviving forever. Hence $\Sigma=\infty$ implies $L=1$.</p>
<p>Finally, when $\Sigma=\infty$, the negative drift of $\log y$ dominates its Brownian term, so $y\to0$. Both boundary points then reach their singularities at $\tau(u)$. We have proved both event identifications. Bounded convergence in the martingale $f(r)$ now gives $\mathbb P(L=1)=f(u/v)$.</p>

## From the flow to the boundary hitting law {#section-boundary-law}

<p>Let $\gamma$ be a trace generating the Loewner hulls and put $X=\inf([1,\infty)\cap\gamma[0,\infty))$, with $\inf\varnothing=\infty$. The geometric comparison used in Rohde–Schramm Lemma 6.6 is the following: for each $s&gt;1$, the ratio $(g_t(1)-U_t)/(g_t(s)-U_t)$ tends to one on $\{X&gt;s\}$ and to zero on $\{X&lt;s\}$. The paper obtains the first limit from extremal distance and the second from the strict inequality of swallowing times. This comparison and the existence of the trace are explicit inputs here; the diffusion calculation alone does not prove them.</p>

<a id="tag-2L0Z" data-assertion="proposition" data-title="The trace boundary hitting law is a beta distribution under the stated geometric comparison"></a>
<p>For $4&lt;\kappa&lt;8$, assume the trace exists, its law is invariant under dilation, and the preceding geometric comparison holds. Then $1&lt;X&lt;\infty$ almost surely, $1/X$ has the beta distribution with parameters $a=1-4/\kappa$ and $c=8/\kappa-1$, and for $s\geq1$,</p>
<div class="math-display">$$\mathbb P(X\geq s)=I_{1/s}(a,c)
=\frac{4^{1-4/\kappa}\sqrt\pi}
{\Gamma(2-4/\kappa)\Gamma(4/\kappa-1/2)}
s^{4/\kappa-1}\,
{}_2F_1\left(1-\frac4\kappa,2-\frac8\kappa;2-\frac4\kappa;\frac1s\right).$$</div>
<p>In particular, the distribution has no atoms and its tail is asymptotic to $s^{-a}/(aB(a,c))$.</p>
<p><em>Proof.</em> First exclude an atom at any $s&gt;1$. For $1&lt;s'&lt;s$, put $d=s/s'$, so $1&lt;d&lt;s$, and define $X_d=\inf([d,\infty)\cap\gamma[0,\infty))$. The event $X=s$ implies $X_d=s$. Dilation invariance gives $X_d\overset{\mathrm{law}}=dX$, whence</p>
<div class="math-display">$$\mathbb P(X=s')=\mathbb P(X_d=s)\geq\mathbb P(X=s).$$</div>
<p>A positive atom would give arbitrarily many distinct atoms of at least the same mass. Thus $\mathbb P(X=s)=0$. The geometric input and KQIN now identify $\{X&gt;s\}$ with the ratio's terminal value one, up to a null event. This proves the beta-integral formula for $s&gt;1$. Letting $s\downarrow1$ and $s\to\infty$ gives $X&gt;1$ and $X&lt;\infty$ almost surely, respectively.</p>
<p>Expanding $(1-q)^{c-1}$ in the beta integral gives</p>
<div class="math-display">$$I_r(a,c)=\frac{r^a}{aB(a,c)}\,{}_2F_1(a,1-c;a+1;r).$$</div>
<p>The duplication formula for the gamma function rewrites $1/(aB(a,c))$ as the displayed constant. The tail asymptotic follows directly by replacing $(1-q)^{c-1}$ by its limit one as $q\downarrow0$. These are ordinary beta and gamma identities.</p>
<p>The distinction between the two preceding results is useful: KQIN is a theorem about boundary flows with its endpoint classification proved here; 2L0Z is the trace interpretation under an expressly stated geometric input. Neither result constructs a percolation scaling limit or supplies the terminal conditioning needed in <a href="/articles/continuum-connection-densities/#section-terminal-formula">the continuum connection-density argument</a>.</p>


## Interior points below kappa eight {#section-interior-lifetimes}

<p>The trace theorem <a href="/tag/MN2A/">MN2A</a> and the simplicity theorem <a href="/tag/CKFH/">CKFH</a> now allow a geometric interpretation of the interior lifetime. Let $\Gamma=\gamma[0,\infty)$ and $K_t=\overline{\mathbb H\setminus D_t}$.</p>

<a id="tag-O0MI" data-assertion="theorem" data-title="A fixed interior point is never reached below kappa eight and its lifetime changes at kappa four"></a>
<p>Let $0&lt;\kappa&lt;8$ and fix $z\in\mathbb H$. Almost surely $\operatorname{dist}(z,\Gamma)&gt;0$. If $0&lt;\kappa\leq4$, then $\tau(z)=\infty$. If $4&lt;\kappa&lt;8$, then $\tau(z)&lt;\infty$ and there is a random $r&gt;0$ such that</p>
<div class="math-display">$$B(z,r)\subset\mathbb H\setminus\Gamma,\qquad
\tau(w)=\tau(z)\quad\text{for every }w\in B(z,r).$$</div>
<p>In the latter case the entire disk lies in the interior of $K_{\tau(z)}$: the point is swallowed in a region missed by the trace, rather than hit by the trace.</p>

<p><em>Proof.</em> Choose $p\in(0,1-\kappa/8)$. The small-ball estimate <a href="/tag/VEZ7/">VEZ7</a>, with the trace hypothesis supplied by MN2A, gives</p>
<div class="math-display">$$\mathbb P\bigl(\operatorname{dist}(z,\Gamma)&lt;\varepsilon\bigr)
\leq C_{z,p}\varepsilon^p$$</div>
<p>for sufficiently small $\varepsilon&gt;0$. Letting $\varepsilon\downarrow0$ proves that the distance is strictly positive almost surely. In the range $0&lt;\kappa\leq4$, CKFH gives $D_t=\mathbb H\setminus\gamma[0,t]$ for every $t$. Thus this fixed point belongs to every $D_t$, and its lifetime is infinite.</p>

<p>Now take $4&lt;\kappa&lt;8$. The lifetime is finite by 6DV8. On the event where both conclusions hold, choose</p>
<div class="math-display">$$0&lt;r&lt;\min\{\operatorname{Im}z,\operatorname{dist}(z,\Gamma)\}.$$</div>
<p>The disk $B(z,r)$ misses the full trace and the real line. For any $s&lt;\tau(z)$, it lies in one component of $\mathbb H\setminus\gamma[0,s]$ and contains $z\in D_s$. Hence the whole disk lies in $D_s$. At time $\tau(z)$ the same disk lies in one component of $\mathbb H\setminus\gamma[0,\tau(z)]$, but that component contains $z\notin D_{\tau(z)}$. It is therefore a bounded component, and the disk is disjoint from $D_{\tau(z)}$. These two facts give $\tau(w)\geq\tau(z)$ and $\tau(w)\leq\tau(z)$, respectively, for every point of the disk. The disk is an open subset of the hull at that time, proving the last assertion.</p>

<p>The first range proves Rohde–Schramm Exercise 6.7, and the second supplies the interior-point assertion of Theorem 6.4. The probability-one event may depend on the fixed point $z$. In particular the infinite-lifetime assertion is not simultaneous over all interior points: random points on the trace do have finite lifetime. The exclusion of $\kappa=0$ is also necessary. For its deterministic vertical slit, a point $iy$, $y&gt;0$, is hit at time $y^2/4$.</p>

## Filled regions appear immediately {#section-positive-area}

<a id="tag-CPJC" data-assertion="corollary" data-title="For kappa between four and eight every positive-time hull has nonempty interior but its boundary and trace have zero area"></a>
<p>For $4&lt;\kappa&lt;8$, almost surely every positive-time hull $K_t$ contains an open disk in $\mathbb H$. In particular, simultaneously for all $t&gt;0$,</p>
<div class="math-display">$$0&lt;\operatorname{area}(K_t)&lt;\infty,\qquad
\operatorname{area}(\partial K_t)=0,\qquad
\operatorname{area}(\Gamma)=0.$$</div>

<p><em>Proof.</em> Let $A_t$ be the event that $K_t\cap\mathbb H$ has nonempty interior. It is measurable: it is enough to ask for a closed disk with rational centre and positive rational radius, contained in $\mathbb H$, whose points lie in $K_t$. Since $K_t$ is closed, membership of a countable dense subset of each such disk suffices, and each membership event is $\{\tau(w)\leq t\}$. The hulls increase, so the events $A_t$ increase as well.</p>

<p>Apply O0MI to the single fixed point $i$. Almost surely some finite-time hull contains an open disk, and thus $\mathbb P(\bigcup_{n\geq1}A_n)=1$. Brownian scaling gives $K_t\overset{\mathrm{law}}=\sqrt t\,K_1$ for every $t&gt;0$, so $\mathbb P(A_t)=\delta$ is independent of $t$. Continuity of probability along the increasing events $A_n$ gives $\delta=1$. Intersect over positive rational times. For any $t&gt;0$, a smaller rational time already has an interior disk, which remains in $K_t$. This proves the simultaneous assertion.</p>

<p>A nonempty open disk has positive area, and finite-time Loewner hulls are bounded. Their boundaries and the full trace have zero area by <a href="/tag/NHWR/">NHWR</a>. This proves the displayed claims.</p>

<p>The disk here need not be near the origin. This conclusion does not supply the stronger origin-engulfment assertion of Rohde–Schramm Lemma 7.3, which requires a neighborhood of zero inside every positive-time hull. The boundary-interval geometry and the remaining transience argument for $4&lt;\kappa&lt;8$ are still separate.</p>


## The boundary geometry and transience inputs {#section-boundary-geometry-update}

<p>The geometric input retained in 2L0Z is now supplied by <a href="/tag/E5JX/">E5JX</a> and <a href="/tag/U8XU/">U8XU</a>. At the lifetime of a positive boundary point, backward flow places the tip to its right. Local Schwarz reflection shows that each preceding compact interval is separated from the future domain. Equality of swallowing times is therefore exactly the event in the beta tail formula. Together with the already proved trace theorem, this establishes the boundary hitting law and the real-point part of Theorem 6.4 for kappa between four and eight. The earlier conditional statement is retained with its original hypotheses.</p>

<p>The same interval argument supplies the stronger conclusion that CPJC did not prove: <a href="/tag/ZI7H/">ZI7H</a> gives a neighbourhood of the origin inside every positive-time hull. The preimages of zero at a finite boundary swallowing time are covered by one fixed negative interval on an event of positive probability; an independent future can swallow that interval. Scaling and the germ law then apply. <a href="/tag/G09W/">G09W</a> proves intermediate-regime transience and simultaneous finite lifetimes of all nonzero points. These are the remaining boundary and origin arguments, with full proofs in the <a href="/articles/sle-boundary-swallowing/">boundary-swallowing article</a>.</p>
