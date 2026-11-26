---
{
  "id": "embedded-branching-trees",
  "title": "Spatial scales of an embedded branching tree",
  "subtitle": "Occupation, correlation lengths and the probability of reaching a distant box",
  "kind": "model",
  "category": "Models",
  "summary": "Independent nearest-neighbour displacements turn the regular-tree cluster into a branching walk with a different offspring law at its root. Exact occupation formulas give both correlation lengths, while a comparison function and a second-moment bound give the critical spatial-radius exponent.",
  "context": [
    "Fix integers d at least one and n at least two. The initial particle has Binomial(n+1,p) children, and later particles have Binomial(n,p) children.",
    "Each child independently takes a uniformly chosen nearest-neighbour step in the lattice. Displacements and offspring counts are independent.",
    "Occupation counts particles with multiplicity. It is not a percolation connection probability, and distinct particles may occupy the same site.",
    "The finite-cluster field includes the extinction indicator. Its normalization, and the exceptional root law, are retained throughout.",
    "Spatial Green asymptotics at criticality require d at least three. The correlation-length and radius statements have their own explicit parameter ranges."
  ],
  "related": ["regular-tree-percolation", "branching-random-walk", "critical-exponents", "directional-correlation-length"],
  "sourceIds": ["heydenreich-hofstad"],
  "aliases": ["branching walk correlation length", "critical branching walk radius", "embedded regular tree"],
  "prototypeUses": []
}
---

## Occupation with the root counted once {#section-occupation}

<p>Write $r=n+1$, $p_c=1/n$ and $D(\pm e_i)=1/(2d)$. For $0\le\mu\le1$, let</p>
<div class="math-display">$$C_\mu(x)=\sum_{j\ge0}\mu^jD^{*j}(x),\qquad D^{*0}(x)=\mathbf1_{\{x=0\}}.$$</div>
<p>Let $L_x$ count all particles at $x$, and let $S$ be the total number of particles. Put $G_p^{\mathrm f}(x)=\mathbb E[L_x;S<\infty]$. Use the extinction quantities from <a href="/tag/0JTK/">0JTK</a>:</p>
<div class="math-display">$$q=(1-p+pq)^n,\qquad w=1-p+pq,\qquad
q_0=w^r,\qquad p_*=\frac{pq}{w},\qquad \mu=np_*,$$</div>
<p>where $q$ is the least fixed point. Here $0\le p<1$; thus $q_0>0$ and the conditional law is defined.</p>

<a id="tag-8KZO" data-assertion="proposition" data-title="Occupation and second-moment length for an embedded regular-root branching tree"></a>
<p>For every $x\in\mathbb Z^d$,</p>
<div class="math-display">$$G_p^{\mathrm f}(x)=q_0\left[
\mathbf1_{\{x=0\}}+\frac rn\sum_{j\ge1}\mu^jD^{*j}(x)\right].$$</div>
<p>This is an equality of nonnegative extended quantities. For $p\ne p_c$, $\mu<1$, and it gives</p>
<div class="math-display">$$
\sum_xG_p^{\mathrm f}(x)=q_0\frac{1+p_*}{1-np_*},\qquad
\sum_x|x|^2G_p^{\mathrm f}(x)=q_0\frac{rp_*}{(1-np_*)^2}.
$$</div>
<p>Consequently the length defined by the normalized second spatial moment satisfies</p>
<div class="math-display">$$
\xi_2(p)^2:=
\frac{\sum_x|x|^2G_p^{\mathrm f}(x)}{\sum_xG_p^{\mathrm f}(x)}
=\frac{rp_*}{(1-np_*)(1+p_*)},\qquad
\xi_2(p)\sim\frac1{\sqrt{n|p-p_c|}}
$$</div>
<p>as $p\to p_c$ through either side. At criticality, for $d\ge3$,</p>
<div class="math-display">$$G_{p_c}^{\mathrm f}(x)\sim
\frac rn\,\frac{d\,\Gamma(d/2-1)}{2\pi^{d/2}}|x|^{2-d}
\qquad (|x|\to\infty).$$</div>
<p><em>Proof.</em> Extinction depends only on the genealogical tree, so conditioning on it leaves the displacements independent with law $D$. By 0JTK the conditioned initial offspring mean is $rp_*$ and every later offspring mean is $\mu=np_*$. Thus the expected number of particles in generation $j\ge1$ is $rp_*\mu^{j-1}=(r/n)\mu^j$. Their expected spatial distribution is this number times $D^{*j}$, by the induction in <a href="/tag/94E7/">94E7</a>. Generation zero consists of exactly one particle. Sum the generations and multiply by $q_0$.</p>
<p>For a walk of $j$ steps, centering and independence give $\sum_x|x|^2D^{*j}(x)=j$. Tonelli and the geometric sums $\sum_{j\ge1}\mu^j=\mu/(1-\mu)$ and $\sum_{j\ge1}j\mu^j=\mu/(1-\mu)^2$ give both spatial sums. Their ratio gives $\xi_2^2$. The dual-gap equivalent in 0JTK is $1-np_*\sim n|p-p_c|$, while $rp_* /(1+p_*)\to1$, proving the length equivalent.</p>
<p>At criticality $q_0=1$ and $\mu=1$. Away from the origin the occupation is $(r/n)C_1(x)$. The nearest-neighbour step covariance is $I/d$, so <a href="/tag/02EB/">02EB</a> gives the stated spatial equivalent. The assumption $d\ge3$ is needed for this finite Green function; a finite critical family tree may still have infinite expected occupation on a recurrent walk.</p>
<p>For a homogeneous branching walk with $\operatorname{Binomial}(n,p)$ offspring also at the initial particle, the corresponding field below criticality is $C_{np}$, without the factor $r/n$. For the regular-root model it is instead</p>
<div class="math-display">$$G_p^{\mathrm f}=\frac rn C_{np}-\frac1n\mathbf1_{\{0\}}
\qquad(0\le p\le p_c),$$</div>
<p>with the critical identity understood through its nonnegative generation sum. The subtraction corrects the count of the initial particle. Already at $p=0$ its omission would give mass $r/n$ at the origin instead of one. The <a href="/errata/heydenreich-hofstad/#generation-zero-occupation">manuscript erratum</a> records this distinction.</p>
<p>The Fourier statement also has a precise meaning. For $\mu<1$, absolute summability gives $\widehat C_\mu(k)=(1-\mu\widehat D(k))^{-1}$. When $d\ge3$, these densities converge in $L^1$ as $\mu\uparrow1$ to $(1-\widehat D(k))^{-1}$: where $\widehat D\ge0$ use its integrable critical majorant, and where $\widehat D<0$ use the bound one. Fourier coefficients therefore converge to $C_1(x)$. Since $1-\widehat D(k)\sim |k|^2/(2d)$, the critical singularity is $2d/|k|^2$. For the regular-root field its density is $(1+\widehat D(k)/n)/(1-\widehat D(k))$, with leading coefficient multiplied by $r/n$. This is an Abel-limit argument; at frequencies with $\widehat D=-1$ the undamped geometric series is not ordinarily convergent.</p>

## Exponential decay on a coordinate axis {#section-axis-length}

<a id="tag-TX3U" data-assertion="theorem" data-title="The exact axis correlation length of a nearest-neighbour branching walk"></a>
<p>For $0<\mu<1$ and $d\ge1$, put</p>
<div class="math-display">$$a(\mu)=\operatorname{arcosh}\!\left(\frac d\mu-(d-1)\right)>0.$$</div>
<p>Then</p>
<div class="math-display">$$-\lim_{R\to\infty}\frac1R\log C_\mu(Re_1)=a(\mu),\qquad R\in\mathbb N.$$</div>
<p>For the finite-cluster field in 8KZO, with $0<p<1$ and $p\ne p_c$, the coordinate correlation length is therefore</p>
<div class="math-display">$$
\xi(p):=\left[-\lim_{R\to\infty}\frac1R\log G_p^{\mathrm f}(Re_1)\right]^{-1}
=\frac1{a(np_*)}
\sim\frac1{\sqrt{2dn|p-p_c|}}
$$</div>
<p>as $p\to p_c$ from either side.</p>
<p><em>Proof.</em> Tilt the nearest-neighbour law by</p>
<div class="math-display">$$D_a(z)=\mu e^{az_1}D(z),\qquad a=a(\mu).$$</div>
<p>Its total mass is $\mu(\cosh a+d-1)/d=1$. Its drift is $ve_1$, where $v=\mu\sinh(a)/d\in(0,1)$. For every time $t$,</p>
<div class="math-display">$$D_a^{*t}(Re_1)=\mu^t e^{aR}D^{*t}(Re_1),\qquad
C_\mu(Re_1)=e^{-aR}G_a(Re_1),$$</div>
<p>where $G_a=\sum_{t\ge0}D_a^{*t}$. We show that $R^{-1}\log G_a(Re_1)\to0$.</p>
<p>For a sufficiently small $\delta>0$, the positive first-coordinate drift gives $\mathbb E_{D_a}e^{-\delta Z_1}<1$. Hence</p>
<div class="math-display">$$D_a^{*t}(0)\le
\mathbb E_{D_a}e^{-\delta (Z_{1,1}+\cdots+Z_{t,1})}
=\bigl(\mathbb E_{D_a}e^{-\delta Z_1}\bigr)^t,$$</div>
<p>so $G_a(0)<\infty$. The strong Markov property at the first visit to $x$ and translation invariance give $G_a(x)=\mathbb P_0(\text{ever hit }x)G_a(0)\le G_a(0)$, which is a uniform upper bound.</p>
<p>For the lower bound, choose $t_R=R/v+O(1)$ with $t_R\equiv R\pmod2$. For each $i\ge2$, choose equal counts of $+e_i$ and $-e_i$ within one of their common expected count $t_RD_a(e_i)$. The remaining two counts are determined by their sum and by their difference $R$. Parity makes them integers, and the choice of $t_R$ puts each within $O(1)$ of its expected count. All counts are nonnegative for large $R$, since every step has positive probability. These counts give endpoint $Re_1$. Stirling's formula for this single multinomial term gives probability at least $c\,t_R^{-(2d-1)/2}$ for all sufficiently large $R$, with $c>0$ depending on the fixed tilted law. Thus $G_a(Re_1)$ is bounded below by a polynomial in $R$, proving the logarithmic limit.</p>
<p>For $R\ge1$, 8KZO gives $G_p^{\mathrm f}(Re_1)=q_0(r/n)C_{np_*}(Re_1)$. Its positive prefactor does not affect the exponential rate. Finally, $\cosh a-1=d(1-\mu)/\mu$ implies $a(\mu)\sim\sqrt{2d(1-\mu)}$ as $\mu\uparrow1$. Apply 0JTK's dual-gap equivalent. The second-moment and exponential lengths have the same exponent but different leading constants under the definitions used here.</p>

## Reaching a distant box {#section-radius}

<a id="tag-MC4U" data-assertion="theorem" data-title="Critical nearest-neighbour branching walk reaches distance R with probability of order R to the minus two"></a>
<p>At $p=p_c$, let $\mathcal R$ be the largest $\ell^\infty$ distance of any particle from its initial location. For the homogeneous process with offspring law $\operatorname{Binomial}(n,1/n)$, and also for the regular-root process above, there are constants $0<c\le C<\infty$ such that</p>
<div class="math-display">$$cR^{-2}\le\mathbb P(\mathcal R\ge R)\le CR^{-2}
\qquad(R\in\mathbb N,\ R\ge1).$$</div>
<p>This holds in every $d\ge1$. In the reciprocal convention of <a href="/tag/BLNL/">BLNL</a>, the spatial one-arm exponent is $1/2$. No exact asymptotic constant is asserted.</p>
<p><em>Proof.</em> First use the homogeneous offspring law, whose variance is $\sigma^2=(n-1)/n$. If $Z_t$ is its generation size, conditioning on $Z_t$ gives</p>
<div class="math-display">$$\mathbb E Z_t=1,\qquad
\mathbb E Z_{t+1}^2=\mathbb E Z_t^2+\sigma^2,\qquad
\mathbb E Z_t^2=1+\sigma^2t.$$</div>
<p>Let $Y_t$ count generation-$t$ particles outside the cube of radius $R-1$. By 94E7, $\mathbb E Y_t=\mathbb P(\|W_t\|_\infty\ge R)$ for a simple random walk $W$. Take $t=4dR^2$. Its first coordinate has</p>
<div class="math-display">$$\mathbb E W_{t,1}^2=\frac td,\qquad
\mathbb E W_{t,1}^4=\frac td+\frac{3t(t-1)}{d^2}\le\frac{4t^2}{d^2}.$$</div>
<p>These follow by expanding the sums of centered independent coordinate steps. Cauchy–Schwarz applied to $W_{t,1}^2$ above the threshold $R^2$ gives</p>
<div class="math-display">$$\mathbb P(|W_{t,1}|\ge R)\ge
\frac{(\mathbb E W_{t,1}^2-R^2)^2}{\mathbb E W_{t,1}^4}\ge\frac9{64}.$$</div>
<p>Thus $\mathbb E Y_t\ge9/64$. Since $Y_t\le Z_t$, another application of Cauchy–Schwarz gives</p>
<div class="math-display">$$\mathbb P(\mathcal R\ge R)\ge
\mathbb P(Y_t>0)\ge\frac{(\mathbb E Y_t)^2}{\mathbb E Y_t^2}
\ge\frac{c}{1+\sigma^2t}\ge c'R^{-2}.$$</div>
<p>For the upper bound, project onto one coordinate. Its step kernel $P$ has probabilities $1/(2d)$ for each of $+1,-1$ and the remaining probability for zero. The branching map is</p>
<div class="math-display">$$F(s)=1-(1-s/n)^n\le s-bs^2\quad(0\le s\le1),\qquad
b=\frac{n-1}{2n}(1-1/n)^{n-2}>0.$$</div>
<p>The inequality follows by integrating $F''(s)=-(n-1)(1-s/n)^{n-2}/n$ twice, using $F(0)=0$ and $F'(0)=1$. Choose $A\ge\max(4,6/b)$ and define</p>
<div class="math-display">$$
h(j)=\begin{cases}
\min\{1,g(j)\},& |j|<R,\\
1,&|j|\ge R,
\end{cases}
\qquad
g(j)=A\left((R-j)^{-2}+(R+j)^{-2}\right).
$$</div>
<p>We claim $F(Ph(j))\le h(j)$ at every interior site. It is immediate when $h(j)=1$. Otherwise both boundary distances exceed $\sqrt A\ge2$, so $j$ and its neighbours are interior and $Ph(j)\le Pg(j)$. For $t\ge2$,</p>
<div class="math-display">$$
(t-1)^{-2}+(t+1)^{-2}-2t^{-2}
=\frac{2(3t^2-1)}{t^2(t^2-1)^2}\le12t^{-4}.
$$</div>
<p>Applying this to the two terms of $g$ yields</p>
<div class="math-display">$$
Ph(j)-h(j)\le Pg(j)-g(j)
\le\frac{6A}{d}\left((R-j)^{-4}+(R+j)^{-4}\right)
\le\frac6A h(j)^2.
$$</div>
<p>If $Ph(j)<h(j)$, use $F(Ph(j))\le Ph(j)$. Otherwise use the quadratic bound and $6/A\le b$ to obtain $F(Ph(j))\le h(j)$. This proves the claim.</p>
<p>The probability of reaching either boundary by generation $t$ starts from zero at interior sites and one at boundary sites. Its recursion at an interior site is $u_{t+1}=F(Pu_t)$. Monotonicity and the preceding comparison give $u_t\le h$ by induction, and then the same bound for ever reaching the boundary. At zero this is at most $2A/R^2$. A union bound over the $d$ coordinates proves the upper bound for the homogeneous process.</p>
<p>For the regular-root process, condition on its potential first-generation branches. A particle at distance at least $R$ must, for $R\ge2$, belong to a child subtree reaching relative distance at least $R-1$. The upper bound therefore follows by a union bound over the $r$ possible branches. For the lower bound, require one fixed branch to be open, an event of probability $1/n$, and its independent forward branching walk to reach relative distance $R+1$. Since the first displacement has norm one, this forces distance at least $R$ from the original root. Adjust constants to include $R=1$.</p>
<p>The bound concerns a branching walk with independent displacements and repeated visits allowed. It supplies no percolation radius estimate without an additional comparison theorem.</p>



## The prefactor in axis decay {#section-axis-prefactor}

<a id="tag-S78W" data-assertion="theorem" data-title="The killed nearest-neighbour Green function has an explicit axis prefactor"></a>
<p>Fix $d\ge1$ and $0&lt;\mu&lt;1$, and write $a=a(\mu)$ as in TX3U. For $k'=(k_2,\ldots,k_d)$ on the $(d-1)$-dimensional frequency torus, put</p>
<div class="math-display">$$
b(k')=\operatorname{arcosh}\!\left(\frac d\mu-\sum_{j=2}^d\cos k_j\right).
$$</div>
<p>For every integer $R\ge0$,</p>
<div class="math-display">$$
C_\mu(Re_1)=\frac d\mu
\int_{[-\pi,\pi]^{d-1}}
\frac{e^{-Rb(k')}}{\sinh b(k')}\,\frac{dk'}{(2\pi)^{d-1}}.
$$</div>
<p>In particular, as $R\to\infty$ through integers,</p>
<div class="math-display">$$
C_\mu(Re_1)=\frac d\mu\,
\frac{(\sinh a)^{(d-3)/2}}{(2\pi R)^{(d-1)/2}}
e^{-aR}\left[1+O_{d,\mu}(R^{-1})\right].
$$</div>
<p>The parameter $\mu$ is fixed in this error estimate. In dimension one the integral has no variables and gives the exact identity $C_\mu(R)=e^{-aR}/\sqrt{1-\mu^2}$.</p>
<p><em>Proof.</em> Since $\mu&lt;1$, Fourier inversion of the summable walk series is valid in every dimension. For $b&gt;0$, the geometric series gives the Poisson-kernel identity</p>
<div class="math-display">$$
\frac1{\cosh b-\cos t}
=\frac1{\sinh b}\left(1+2\sum_{j\ge1}e^{-jb}\cos jt\right).
$$</div>
<p>Its $R$th Fourier coefficient is $e^{-Rb}/\sinh b$. The identity</p>
<div class="math-display">$$
1-\mu\widehat D(k)=\frac\mu d\bigl(\cosh b(k')-\cos k_1\bigr)
$$</div>
<p>therefore proves the integral formula after integrating in $k_1$. All the denominators are bounded away from zero for the fixed $\mu$.</p>
<p>For $d\ge2$, $b$ has its unique minimum on the torus at $k'=0$, and this minimum is $a&gt;0$. Taylor expansion gives</p>
<div class="math-display">$$
b(k')=a+\frac{|k'|^2}{2\sinh a}+O_{d,\mu}(|k'|^4),\qquad
\frac1{\sinh b(k')}=\frac1{\sinh a}+O_{d,\mu}(|k'|^2).
$$</div>
<p>Outside a small neighbourhood of zero, the integral is $O(e^{-(a+c)R})$ for some $c&gt;0$. Inside it, subtract the Gaussian with phase $|k'|^2/(2\sinh a)$ and constant amplitude $1/\sinh a$. By making the neighbourhood smaller, the quartic phase error can be absorbed into a fixed fraction of the quadratic decay. The difference of the two integrands is then bounded by</p>
<div class="math-display">$$
C e^{-aR}\bigl(|k'|^2+R|k'|^4\bigr)e^{-cR|k'|^2}.
$$</div>
<p>Its integral is $O(e^{-aR}R^{-(d-1)/2-1})$. The Gaussian main term, with the normalized measure in the formula, is</p>
<div class="math-display">$$
\frac{e^{-aR}}{\sinh a}
\left(\frac{\sinh a}{2\pi R}\right)^{(d-1)/2}.
$$</div>
<p>Multiplication by $d/\mu$ gives the result. For $d=1$, $\cosh a=1/\mu$ implies $\mu\sinh a=\sqrt{1-\mu^2}$, proving the exact expression. $\square$</p>
<p>For the finite-cluster occupation in 8KZO and $R\ge1$, multiply this expression by $q_0r/n$ and set $\mu=np_*$. The exceptional root changes the amplitude but neither the exponential rate nor the power of $R$.</p>

## The near-critical spatial profile {#section-massive-crossover}

<a id="tag-LEJR" data-assertion="theorem" data-title="A uniform massive continuum approximation describes the near-critical nearest-neighbour Green function"></a>
<p>Fix an integer $d\ge3$ and $0&lt;\mu_0&lt;1$. For $\mu_0\le\mu\le1$, put</p>
<div class="math-display">$$
m=\sqrt{\frac{2d(1-\mu)}\mu},\qquad
\Phi_d(z)=\frac{2d}{(4\pi)^{d/2}}
\int_0^\infty s^{-d/2}
\exp\!\left(-\frac1{4s}-z^2s\right)\,ds
\quad(z\ge0).
$$</div>
<p>Uniformly in $\mu$ and nonzero $x\in\mathbb Z^d$, with $R=|x|$,</p>
<div class="math-display">$$
C_\mu(x)=\frac{R^{2-d}}\mu\,\Phi_d(mR)
+O_{d,\mu_0}(R^{-d}).
$$</div>
<p>The profile is positive and continuous on $[0,\infty)$, and</p>
<div class="math-display">$$
\Phi_d(0)=\frac{d\,\Gamma(d/2-1)}{2\pi^{d/2}},\qquad
\Phi_d(z)\sim\frac d{(2\pi)^{(d-1)/2}}
z^{(d-3)/2}e^{-z}\quad(z\to\infty).
$$</div>
<p>For each fixed $M&lt;\infty$, the displayed approximation has relative error $O_{d,\mu_0,M}(R^{-2})$ whenever $mR\le M$. Thus, if $R\to\infty$ and $mR\to z&lt;\infty$, then $R^{d-2}C_\mu(x)\to\Phi_d(z)$, in any sequence of lattice directions.</p>
<p><em>Proof.</em> Use the inverse Fourier convention $(2\pi)^{-d}\int e^{ik\cdot x}\,dk$. Set</p>
<div class="math-display">$$
Q(k)=2\sum_{j=1}^d(1-\cos k_j)=2d(1-\widehat D(k)).
$$</div>
<p>Then $(1-\mu\widehat D)^{-1}=(2d/\mu)(m^2+Q)^{-1}$. The Fourier representation remains valid at $\mu=1$ by the Abel-limit argument given after 8KZO. The restriction $d&gt;2$ makes its singularity integrable.</p>
<p>Choose a smooth cutoff $\chi$ supported in a sufficiently small ball about zero inside the frequency cube, equal to one near zero. In this ball $Q(k)\asymp|k|^2$ and $Q(k)=|k|^2+O(|k|^4)$. The difference</p>
<div class="math-display">$$
E_m(k)=\frac1{m^2+Q(k)}-\frac1{m^2+|k|^2}
=\frac{|k|^2-Q(k)}{(m^2+Q(k))(m^2+|k|^2)}
$$</div>
<p>satisfies, for every multi-index $\alpha$ and $k\ne0$,</p>
<div class="math-display">$$
|\partial^\alpha E_m(k)|\le C_\alpha|k|^{-|\alpha|},
$$</div>
<p>with constants independent of $m\ge0$. Indeed, the numerator and its derivatives have order $|k|^{4-|\alpha|}$. Repeated differentiation of either inverse denominator costs at most a factor $C|k|^{-1}$ per derivative while retaining that inverse denominator. Leibniz's rule reduces the bound to $|k|^4/(m^2+c|k|^2)^2\le C$. Applying <a href="/tag/C5GY/">C5GY</a> with $\beta=0$ and an integer $N&gt;d$ gives $\mathcal F^{-1}(\chi E_m)(x)=O(R^{-d})$ uniformly in $m$.</p>
<p>The remaining torus symbol $(1-\chi)/(m^2+Q)$ is smooth and periodic, with uniformly bounded derivatives for $0\le m\le[2d(1-\mu_0)/\mu_0]^{1/2}$. Its coefficients at integer $x$ decrease faster than every inverse power, uniformly in this interval. The same conclusion holds for the inverse of $(1-\chi)/(m^2+|k|^2)$ on $\mathbb R^d$: its derivatives of any order $N&gt;d-2$ are uniformly integrable, since it vanishes near zero and these derivatives are $O(|k|^{-2-N})$ at infinity. Integrating by parts in a largest coordinate of $x$, in the distributional form used in C5GY, gives the required decay. This argument does not require the massive symbol to be homogeneous.</p>
<p>It follows that</p>
<div class="math-display">$$
C_\mu(x)=\frac{2d}\mu\,g_m(x)+O_{d,\mu_0}(R^{-d}),\qquad
g_m(x)=\mathcal F^{-1}\!\left(\frac1{m^2+|k|^2}\right)(x).
$$</div>
<p>The Gaussian transform and the identity $(m^2+|k|^2)^{-1}=\int_0^\infty e^{-t(m^2+|k|^2)}\,dt$ give, away from zero,</p>
<div class="math-display">$$
g_m(x)=\int_0^\infty e^{-m^2t}(4\pi t)^{-d/2}e^{-R^2/(4t)}\,dt.
$$</div>
<p>The transform identity is justified first against Schwartz functions by absolute Fubini; $|k|^{-2}$ is locally integrable for $d&gt;2$. The time integral converges locally uniformly off the origin, including at $m=0$. Substituting $t=R^2s$ proves the asserted approximation.</p>
<p>At $z=0$, the substitution $u=1/(4s)$ evaluates the profile in terms of $\Gamma(d/2-1)$. The same integrable function at $z=0$ dominates the integrands for all $z\ge0$, proving continuity. Positivity gives a positive minimum on each compact interval, and hence the stated relative error. If $mR$ is bounded and $R\to\infty$, then $m\to0$ and $\mu\to1$, giving the scaling limit.</p>
<p>For the large-$z$ equivalent, substitute $u=2zs$ to obtain</p>
<div class="math-display">$$
\Phi_d(z)=\frac{2d(2z)^{d/2-1}}{(4\pi)^{d/2}}
\int_0^\infty u^{-d/2}
\exp\!\left[-\frac z2(u+u^{-1})\right]du.
$$</div>
<p>The phase $(u+u^{-1})/2$ has its unique minimum $1$ at $u=1$ and second derivative $1$ there. On a fixed neighbourhood of one, rescaling $u-1$ by $z^{-1/2}$ gives $e^{-z}\sqrt{2\pi/z}$ for the integral. The complement is exponentially smaller: on a compact set away from one the phase exceeds one, while the ends are controlled by $u/2$ and $1/(2u)$, respectively. Combining the constants proves the equivalent. $\square$</p>
<p>The relative approximation is restricted to bounded $mR$. Its absolute remainder does not imply a relative estimate when the profile becomes exponentially small. In particular, for fixed $\mu&lt;1$ the exact lattice rate is</p>
<div class="math-display">$$
a(\mu)=2\operatorname{arsinh}(m/2)&lt;m,
$$</div>
<p>so the continuum exponential $e^{-mR}$ cannot replace the axis formula in S78W at arbitrarily large distances. At $\mu=1$ the result recovers the leading critical amplitude, with error $O(R^{-d})$; <a href="/tag/IY26/">IY26</a> identifies that error's first directional term. For the regular-root occupation, 8KZO again supplies the factor $q_0r/n$ away from the origin.</p>



## Integrated near-critical diagrams {#section-killed-diagram-link}

<p>The <a href="/articles/infrared-diagrams/#section-killed-diagram-asymptotics">killed-diagram asymptotics</a> compute the corresponding singularities of convolution powers at the origin, including a convergent formula for the constant after subtracting the marginal logarithm. For nearest-neighbour walk, the <a href="/articles/infrared-diagrams/#section-marginal-killing-coefficients">six-dimensional calculation</a> shows how the divergent triangle determines the approach of the finite bubble to its critical value. The distinction between the killing gap and the continuum mass is retained in the constants.</p>



## A frequency scale for the diagrams {#section-shifted-diagram-link}

<p>The <a href="/articles/infrared-diagrams/#section-shifted-marginal-profile">shifted-diagram profile</a> describes frequency shifts comparable to the mass in dimensions four and six. A <a href="/articles/infrared-diagrams/#section-critical-shifted-finite-part">separate critical calculation</a> determines the logarithm and constant term as a nonzero frequency tends to zero. The latter retains the distinction between an Abel limit and an undamped spatial Fourier series.</p>
