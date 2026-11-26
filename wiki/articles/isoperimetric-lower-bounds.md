---
{
  "id": "isoperimetric-lower-bounds",
  "title": "Isoperimetric lower bounds for critical percolation",
  "subtitle": "Boundary crossings, box susceptibility and critical exponents",
  "kind": "method",
  "category": "Critical phenomena",
  "summary": "Averaging boundary crossings over nested cubes bounds the boundary functional by the expected internal cluster size. Criticality then forces a lower bound on box susceptibility and, through finite-window hyperscaling, on the cluster-tail exponent.",
  "context": [
    "Independent bonds on the integer lattice, with symmetric translation-invariant summable intensities.",
    "Critical conclusions require a finite critical intensity.",
    "Internal clusters and intersections of unrestricted clusters with a box are different observables."
  ],
  "related": [
    "boundary-laws",
    "finite-size-sharpness",
    "finite-set-hyperscaling",
    "hierarchical-comparison",
    "cutoff-localization"
  ],
  "sourceIds": [
    "baumler-berger-isoperimetric-2022",
    "hutchcroft-book"
  ],
  "aliases": [
    "Bäumler Berger",
    "isoperimetric critical exponents",
    "averaged two-point lower bound",
    "random box radius",
    "boundary crossing profile"
  ],
  "prototypeUses": []
}
---

## Boundary crossings {#section-profile}

<p>Let $d\geq1$ and let $J(z)=J(-z)\geq0$ for $z\in\mathbb Z^d\setminus\{0\}$, with $\sum_zJ(z)&lt;\infty$. At intensity $\beta\geq0$, the bond from $x$ to $x+z$ is open with probability $q_\beta(z)=1-e^{-\beta J(z)}$, independently over unordered pairs. Put $\Lambda_n=[-n,n]^d\cap\mathbb Z^d$, for integers $n\geq1$, and write</p>
<div class="math-display">$$m_\beta(n)=\mathbb E_\beta|K_0(\Lambda_n)|,\qquad A_\beta(n)=\sum_{x\in\Lambda_n}\mathbb P_\beta(0\leftrightarrow x).$$</div>
<p>Here $K_0(\Lambda_n)$ uses only bonds with both endpoints in $\Lambda_n$. Thus $m_\beta(n)\leq A_\beta(n)$; an unrestricted connection contributing to the latter may leave the box.</p>
<p>Write $\beta_c=\inf\{\beta\geq0:\mathbb P_\beta(|K_0|=\infty)&gt;0\}$, with $\inf\varnothing=\infty$. Translation invariance and countability identify this root threshold with the threshold for an infinite cluster anywhere.</p>

<a id="tag-PTM2" data-assertion="proposition" data-title="A boundary crossing profile controls the average finite-size functional"></a>
<p>Define</p>
<div class="math-display">$$b_\beta(n)=\sum_{z\ne0}q_\beta(z)\min\left\{1,\frac{\|z\|_\infty}{n}\right\},\qquad
\Phi_\beta(S)=\sum_{a\in S}\mathbb P_\beta(0\overset S\longleftrightarrow a)\sum_{b\notin S}q_\beta(b-a).$$</div>
<p>Then</p>
<div class="math-display">$$\frac1n\sum_{k=1}^n\Phi_\beta(\Lambda_k)\leq m_\beta(n)b_\beta(n).$$</div>
<p><em>Proof.</em> Fix $a\in\Lambda_n$ and a displacement $z\ne0$. A bond from $a$ to $a+z$ crosses the boundary of $\Lambda_k$, with $a$ inside, precisely when $\|a\|_\infty\leq k&lt;\|a+z\|_\infty$. Among $k=1,\ldots,n$, the number of such radii is at most $\min\{n,\|z\|_\infty\}$, by the reverse triangle inequality. Also</p>
<div class="math-display">$$\mathbb P_\beta(0\overset{\Lambda_k}\longleftrightarrow a)\leq\mathbb P_\beta(0\overset{\Lambda_n}\longleftrightarrow a).$$</div>
<p>Insert this inequality into the boundary functional, interchange the nonnegative sums, and use the crossing count. Summing the remaining internal connection probabilities over $a$ gives $m_\beta(n)$. All sums are finite or summable since $q_\beta\leq\beta J$. In probabilistic terms, $\Phi_\beta(\Lambda_k)$ is the expected number of open boundary bonds whose inside endpoint connects internally to the root: each such bond is independent of that internal connection event.</p>
<p>The profile retains the actual bond probabilities. If $\sum_z\|z\|_\infty q_\beta(z)&lt;\infty$, for example, it is at most that first moment divided by $n$.</p>

## Power-law boundaries {#section-surface}

<a id="tag-31X5" data-assertion="proposition" data-title="Power-law crossing profiles and the expected boundary of a cube"></a>
<p>Suppose $J(z)\leq C\|z\|_\infty^{-d-\alpha}$ for some $\alpha,C&gt;0$. For fixed finite $\beta&gt;0$ there is a finite constant $C_\beta$, independent of $n$, such that $b_\beta(n)\leq C_\beta f_\alpha(n)$, where</p>
<div class="math-display">$$f_\alpha(n)=\begin{cases}n^{-\alpha},&amp;0&lt;\alpha&lt;1,\\ \log(en)/n,&amp;\alpha=1,\\ n^{-1},&amp;\alpha&gt;1.\end{cases}$$</div>
<p>For any summable translation-invariant bond probabilities, if $\partial\Lambda_n$ denotes the open bonds with exactly one endpoint in the cube, then</p>
<div class="math-display">$$\frac13|\Lambda_n|b_\beta(n)\leq\mathbb E_\beta|\partial\Lambda_n|\leq d|\Lambda_n|b_\beta(n).$$</div>
<p>If also $J(z)\geq c\|z\|_\infty^{-d-\alpha}$ for every $z\ne0$ and some $c&gt;0$, then $b_\beta(n)\asymp f_\alpha(n)$ and $\mathbb E_\beta|\partial\Lambda_n|\asymp n^d f_\alpha(n)$. Constants may depend on the fixed kernel, $d,\alpha,\beta$, but not on $n$.</p>
<p><em>Proof.</em> The shell of radius $l$ has $(2l+1)^d-(2l-1)^d\asymp_d l^{d-1}$ vertices. Splitting the profile at $l=n$ gives</p>
<div class="math-display">$$b_\beta(n)\leq C'\beta\left[\frac1n\sum_{l=1}^n l^{-\alpha}+\sum_{l&gt;n}l^{-1-\alpha}\right]\leq C_\beta f_\alpha(n).$$</div>
<p>The integral comparison for the first sum gives a power, a logarithm, or a bounded sum according as $\alpha&lt;1$, $\alpha=1$, or $\alpha&gt;1$. The second sum is at most $n^{-\alpha}/\alpha$. With both kernel bounds, $J(z)\leq C$ and $q_\beta(z)\geq\beta e^{-\beta C}J(z)$, so the same shell sums give the reverse comparison.</p>
<p>To count boundary pairs, put $h=2n+1$. For fixed $z$, the number of $a\in\Lambda_n$ with $a+z\notin\Lambda_n$ is</p>
<div class="math-display">$$N_n(z)=h^d-\prod_{i=1}^d(h-|z_i|)_+.$$</div>
<p>If $r=\|z\|_\infty$, comparison with a coordinate attaining $r$ and then the union bound over coordinates give</p>
<div class="math-display">$$\min\{1,r/h\}\leq N_n(z)/h^d\leq d\min\{1,r/h\}.$$</div>
<p>Since $n\leq h\leq3n$, multiplication by $q_\beta(z)$ and summation give the asserted bounds. Every unordered boundary pair has exactly one inside endpoint, so this sum counts it once.</p>
<p>The positive logarithm covers $n=1$. The source's $\log n/n$ convention is valid with $n\geq2$; its unrestricted initial-scale quantifier is recorded as a <a href="/errata/baumler-berger-isoperimetric-2022/">provisional endpoint correction</a>. No exponent or large-scale conclusion changes.</p>

## Critical box susceptibility {#section-critical}

<a id="tag-VVB0" data-assertion="theorem" data-title="Criticality forces the inverse crossing-profile lower bound"></a>
<p>Let $\beta_c&lt;\infty$. For every finite $\beta\geq\beta_c$ and every integer $n\geq1$,</p>
<div class="math-display">$$A_\beta(n)\geq m_\beta(n)\geq b_\beta(n)^{-1}.$$</div>
<p>In particular, under the power-law upper bound of 31X5, there is $c_\beta&gt;0$ such that</p>
<div class="math-display">$$m_\beta(n)\geq c_\beta\begin{cases}n^\alpha,&amp;\alpha&lt;1,\\ n/\log(en),&amp;\alpha=1,\\ n,&amp;\alpha&gt;1.\end{cases}$$</div>
<p><em>Proof.</em> Translation invariance and summability give the <a href="/tag/R84Z/">critical boundary inequality</a> $\Phi_{\beta_c}(\Lambda_k)\geq1$. Monotonicity gives the same inequality at $\beta\geq\beta_c$. Averaging it and applying PTM2 yields $1\leq m_\beta(n)b_\beta(n)$, which also proves $b_\beta(n)&gt;0$. The first comparison follows from inclusion of internal connections in unrestricted ones. Apply 31X5 for the power-law conclusion.</p>
<p>A finite critical intensity is an assumption, not a consequence of a power-law upper bound alone. No absence of an infinite cluster at criticality is needed here. The estimate concerns an expectation, not a typical cluster size or a pointwise connection probability.</p>

## Exponent consequences {#section-exponents}

<a id="tag-BNQK" data-assertion="theorem" data-title="Isoperimetric lower bounds on the cluster-tail and two-point exponents"></a>
<p>Assume $0&lt;\beta_c&lt;\infty$ and $J(z)\leq C\|z\|_\infty^{-d-\alpha}$, and put $s=\min\{\alpha,1\}&lt;d$. If for some $0\leq\theta&lt;1$ and finite $A$,</p>
<div class="math-display">$$\mathbb P_{\beta_c}(|K_0|\geq k)\leq A k^{-\theta}\qquad(k\geq1),$$</div>
<p>then $\theta\leq(d-s)/(d+s)$. Consequently, a logarithmic tail exponent $\delta\in(0,\infty]$ satisfying $\mathbb P_{\beta_c}(|K_0|\geq k)=k^{-1/\delta+o(1)}$ obeys</p>
<div class="math-display">$$\delta\geq\frac{d+s}{d-s}.$$</div>
<p>If the unrestricted two-point function has a finite logarithmic exponent $\rho$ in the sense that $\mathbb P_{\beta_c}(0\leftrightarrow x)=\|x\|_\infty^{-d+\rho+o(1)}$ as $\|x\|_\infty\to\infty$, then $\rho\geq s$. The same conclusion holds for an averaged exponent defined by $A_{\beta_c}(n)=n^{\rho+o(1)}$.</p>
<p><em>Proof.</em> Translation makes the tail bound uniform in the root. Apply <a href="/tag/UVQ6/">finite-window hyperscaling</a> to $\Lambda_n$, using $|K_x\cap\Lambda_n|\leq|K_x|$. It gives</p>
<div class="math-display">$$m_{\beta_c}(n)\leq A_{\beta_c}(n)\leq C_{A,\theta,d}\,n^{d(1-\theta)/(1+\theta)}.$$</div>
<p>The lower bound VVB0 is $n^{s+o(1)}$, including the logarithmic case $\alpha=1$. Taking logarithms and dividing by $\log n$ yields $d(1-\theta)/(1+\theta)\geq s$, which rearranges to the claimed bound on $\theta$.</p>
<p>If $1/\delta$ exceeded $(d-s)/(d+s)$, choose $\theta$ strictly between that bound and $\min\{1,1/\delta\}$. The logarithmic tail law supplies a global bound $A k^{-\theta}$ after increasing $A$ to cover finitely many small $k$, a contradiction. This argument does not assume $\delta&gt;1$ in advance and does not replace a logarithmic asymptotic by a bound at its limiting exponent.</p>
<p>For the pointwise claim, suppose $\rho&lt;s$ and choose $u$ with $\max\{\rho,0\}&lt;u&lt;s$. The meaning of the limit as $\|x\|_\infty\to\infty$ gives the uniform bound $\mathbb P_{\beta_c}(0\leftrightarrow x)\leq C_u\|x\|_\infty^{-d+u}$ for nonzero $x$. Shell summation gives $A_{\beta_c}(n)\leq C'_u n^u$, contradicting VVB0. An averaged exponent is compared directly with that lower bound.</p>
<p>Writing $\rho=2-\eta$ recovers the usual notation. The two exponent conclusions are independent: the bound on $\delta$ does not assume existence of $2-\eta$. For $d=1$, $1/3&lt;\alpha&lt;1$, or $d=2$, $\alpha&gt;2/3$, the displayed lower bound on $\delta$ is strictly greater than two. It therefore excludes a cluster-tail exponent equal to two in these regimes, without proving that an exponent exists.</p>

## Matching spatial averages {#section-matching}

<a id="tag-0BJP" data-assertion="corollary" data-title="Two-sided power kernels give the averaged long-range exponent below alpha one"></a>
<p>Suppose $0&lt;\alpha&lt;d$ and</p>
<div class="math-display">$$c\|z\|_\infty^{-d-\alpha}\leq J(z)\leq C\|z\|_\infty^{-d-\alpha}\qquad(z\ne0)$$</div>
<p>for constants $0&lt;c\leq C&lt;\infty$. If $\alpha&lt;1$, then</p>
<div class="math-display">$$m_{\beta_c}(n)\asymp A_{\beta_c}(n)\asymp n^\alpha,\qquad \frac{A_{\beta_c}(n)}{|\Lambda_n|}\asymp n^{-d+\alpha}.$$</div>
<p>If $\alpha=1&lt;d$, then $c_1n/\log(en)\leq m_{\beta_c}(n)\leq A_{\beta_c}(n)\leq C_1n$. In particular, the logarithmic growth exponent of each of $m_{\beta_c}(n)$ and $A_{\beta_c}(n)$ equals $\alpha$ for $0&lt;\alpha\leq1$, with $\alpha&lt;d$ retained.</p>
<p><em>Proof.</em> The lower kernel envelope gives <a href="/tag/KXV3/">a finite positive critical intensity</a> and the <a href="/tag/MRZO/">sharp averaged upper bound</a> $A_{\beta_c}(n)\leq C_1n^\alpha$. The upper envelope gives VVB0. Sandwich $m_{\beta_c}(n)$ between its lower bound and $A_{\beta_c}(n)$; then divide by $(2n+1)^d$ for the spatial average. At $\alpha=1$, $\log\log(en)/\log n\to0$, so the logarithmic exponent is still one.</p>
<p>This is an averaged result. It does not give a lower bound at every vertex, a pointwise asymptotic, or a spatial scaling limit. At $\alpha=1$ it also leaves a logarithmic gap in the two-sided comparison.</p>

## Source correspondence {#section-source}

<p>The <a href="/coverage/sources/isoperimetric-2204.12410v2/">reading map</a> locates the results of Bäumler–Berger in arXiv:2204.12410v2. The crossing-profile proof above counts the radii crossed by each displacement; it also gives the exact cube boundary comparison. Existing rooted damping and finite-window hyperscaling supply the tail-to-box step. Critical flux is already proved separately, so these arguments add no unproved probabilistic input. The endpoint correction remains provisional; source correspondence and Lean associations remain pending.</p>
