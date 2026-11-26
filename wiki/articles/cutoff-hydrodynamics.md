---
{
  "id": "cutoff-hydrodynamics",
  "title": "Cutoff hydrodynamics and moment growth",
  "subtitle": "The direct-merge scale and a low-dimensional contradiction",
  "kind": "method",
  "category": "Critical phenomena",
  "summary": "Rooted exponential damping compares finite-window moments. Explicit moment equations then rule out a largest-cluster scale smaller than the direct-merge scale below the upper critical dimension.",
  "context": [
    "Clusters form a common random partition; observation windows are finite and nonempty.",
    "The cutoff law and the observation window have separate scale parameters.",
    "Differential equations and their probabilistic error bounds are hypotheses where stated."
  ],
  "related": [
    "cutoff-localization",
    "finite-set-hyperscaling",
    "spatial-cutoff-moments",
    "marginal-ode",
    "universal-tightness"
  ],
  "sourceIds": [
    "hutchcroft-book",
    "hutchcroft-lrp-2",
    "perclib-good-scales",
    "perclib-window-hyperscaling",
    "hutchcroft-lrp-3",
    "hutchcroft-lrp-1"
  ],
  "aliases": [
    "hydrodynamic condition",
    "direct-merge scale",
    "bad interval",
    "low-dimensional hyperscaling",
    "rooted damping"
  ],
  "prototypeUses": []
}
---

## The direct-merge scale {#section-scale}

<p>Under the cutoff law at radius $r$, let $Z_{r,R}=\max_x|K_x\cap B_R|$ and</p>
<div class="math-display">$$M(r,R)=\min\{n\geq1:\mathbb P_r(Z_{r,R}\geq n)\leq e^{-1}\},\qquad M_r=M(r,r).$$</div>
<p>The maximum can be taken over roots in $B_R$: every cluster meeting the window contains such a root. Paths may leave the window. In particular, $2\leq M(r,R)\leq|B_R|+1$. The quantity $M(r,Cr)$ retains cutoff $r$ while enlarging the observation window; $M_{Cr}=M(Cr,Cr)$ changes both. Their comparison requires a coupling of the cutoff laws.</p>

<a id="tag-UWLQ" data-assertion="definition" data-title="Hydrodynamic condition at the direct-merge scale"></a>
<p>For parameters $d,\alpha&gt;0$, put $h=(d+\alpha)/2$. The cutoff family satisfies the hydrodynamic condition if $M_r/r^h\to0$ as $r\to\infty$.</p>

<a id="tag-UUQO" data-assertion="proposition" data-title="Independent cross edges identify the direct-merge scale"></a>
<p>Let $A,B$ be disjoint finite vertex sets. Independently for each $u\in A,v\in B$, open the edge $\{u,v\}$ with probability $1-e^{-\beta J(u,v)}$, where $\beta&gt;0$. Suppose, for fixed positive $c_-,c_+$ and $r&gt;0$,</p>
<div class="math-display">$$c_-r^{-d-\alpha}\leq J(u,v)\leq c_+r^{-d-\alpha}.$$</div>
<p>Then the probability $P_{A,B}$ of at least one direct edge satisfies</p>
<div class="math-display">$$1-e^{-\beta c_-r^{-d-\alpha}|A||B|}\leq P_{A,B}\leq1-e^{-\beta c_+r^{-d-\alpha}|A||B|}.$$</div>
<p>In particular, if both cardinalities are between $ar^h$ and $br^h$, for fixed $0&lt;a\leq b&lt;\infty$, the direct-edge probability stays bounded away from zero and one. If $|A||B|=o(r^{d+\alpha})$, it tends to zero.</p>
<p><em>Proof.</em> Distinct pairs between the disjoint sets give distinct edge coordinates. Their closed probabilities multiply, so $P_{A,B}=1-\exp(-\beta\sum_{u\in A,v\in B}J(u,v))$. Bound the sum and use $2h=d+\alpha$.</p>
<p>The same calculation holds conditionally when, given the information determining $A,B$, their cross edges still have the stated independent laws. For example, this applies to sets selected using only the internal edges of two fixed disjoint domains. It cannot be applied without further justification to clusters revealed by exploring the cross edges themselves. For a Euclidean power-law kernel, the displayed two-sided intensity bounds follow when all the cross distances are comparable to $r$.</p>

## Two finite-window moment estimates {#section-moments}

<a id="tag-BZDZ" data-assertion="proposition" data-title="Rooted exponential damping controls higher moments"></a>
<p>Let $X\geq0$ be a random variable, $M,A,b&gt;0$, and suppose</p>
<div class="math-display">$$\mathbb P(X\geq tM)\leq A e^{-bt}\mathbb P(X\geq M)\qquad(t\geq1).$$</div>
<p>For any $p,q&gt;0$ with $\mathbb E X^p&lt;\infty$,</p>
<div class="math-display">$$\mathbb E X^{p+q}\leq D_{p,q}M^q\mathbb E X^p,\qquad D_{p,q}=1+Ae^{-b}+A(p+q)\int_1^\infty t^{p+q-1}e^{-bt}\,dt&lt;\infty.$$</div>
<p><em>Proof.</em> On $\{X\leq M\}$, use $X^{p+q}\leq M^qX^p$. On its complement the layer-cake identity gives</p>
<div class="math-display">$$\mathbb E[X^{p+q}\mathbf1_{\{X&gt;M\}}]=M^{p+q}\mathbb P(X&gt;M)+(p+q)\int_M^\infty t^{p+q-1}\mathbb P(X&gt;t)\,dt.$$</div>
<p>Apply the tail hypothesis, substitute $t=Ms$, and use $M^p\mathbb P(X\geq M)\leq\mathbb E X^p$. This proves both the inequality and finiteness of the higher moment.</p>
<p>For the rooted tightness bound, $A=e$ and $b=1/9$. With $X=|K_o\cap B_R|$ under cutoff $r$, the appropriate quantile is $M(r,R)$. If the laws admit an increasing coupling as the cutoff grows, then $M(r,Cr)\leq M(Cr,Cr)=M_{Cr}$ for $C\geq1$; this follows by comparing every tail probability before taking the integer quantile.</p>

<a id="tag-LQ6Y" data-assertion="proposition" data-title="Largest-intersection quantiles give lower rooted moments"></a>
<p>Let $\Lambda$ be a finite nonempty set in a common random partition. Put $Z=\max_x|K_x\cap\Lambda|$ and $M=\min\{n\geq1:\mathbb P(Z\geq n)\leq e^{-1}\}$. For every $p&gt;0$,</p>
<div class="math-display">$$\sum_{x\in\Lambda}\mathbb E|K_x\cap\Lambda|^p\geq\mathbb E Z^{p+1}\geq\frac{M^{p+1}}{e\,2^{p+1}}.$$</div>
<p>If the full-cluster $p$th moments are the same at every root and equal $m_p$, then $m_p\geq M^{p+1}/(e\,2^{p+1}|\Lambda|)$, allowing extended moments.</p>
<p><em>Proof.</em> The nonempty cluster intersections partition $\Lambda$. If their sizes are $s_i$, counting each root in its own intersection gives $\sum_{x\in\Lambda}|K_x\cap\Lambda|^p=\sum_i s_i^{p+1}\geq Z^{p+1}$. Quantile minimality gives $M\geq2$ and $\mathbb P(Z\geq M-1)&gt;e^{-1}$; also $M-1\geq M/2$. Take expectations. For the last conclusion, bound each intersection by its full cluster.</p>

## Failure of hydrodynamics from explicit moment equations {#section-contradiction}

<a id="tag-XB1X" data-assertion="theorem" data-title="Moment equations contradict a sub-merge largest-cluster scale below three alpha"></a>
<p>Fix $d,\alpha&gt;0$ with $d&lt;3\alpha$, and put $h=(d+\alpha)/2$. Let $m_1,m_2$ be positive locally absolutely continuous functions on $[r_0,\infty)$, and let $M$ be a positive function there. Suppose $m_1(r)\asymp r^\alpha$. Suppose there are constants $a_0,K&gt;0$, $C\geq1$, and measurable functions $a&gt;0$, $e_1,e_2\in[0,1]$ such that $a(r)\sim a_0r^{-\alpha-1}$ and, almost everywhere,</p>
<div class="math-display">$$m_1'=a m_1^2(1-e_1),\qquad m_2'=3a m_1m_2(1-e_2).$$</div>
<p>Assume also, for all sufficiently large $r$,</p>
<div class="math-display">$$e_i(r)\leq K\frac{M(Cr)^2}{r^{d+\alpha}}\quad(i=1,2),\qquad m_2(r)\leq K M(Cr)m_1(r).$$</div>
<p>Then $M(r)/r^h$ does not tend to zero. Equivalently, it is bounded below by a positive constant along an unbounded sequence of radii.</p>
<p><em>Proof.</em> Suppose $M(r)=o(r^h)$. Since $C$ is fixed, both errors tend to zero. The first equation and $m_1(r)\to\infty$ give</p>
<div class="math-display">$$\frac1{m_1(r)}=\int_r^\infty a(s)(1-e_1(s))\,ds\sim\frac{a_0}{\alpha}r^{-\alpha}.$$</div>
<p>Indeed, integrate the derivative of $-1/m_1$ on a finite interval and then send its upper endpoint to infinity; the integrand is asymptotic to the displayed integrable power. It follows that $m_1(r)\sim(\alpha/a_0)r^\alpha$. The second equation now gives $(\log m_2)'=(3\alpha+o(1))/r$ almost everywhere. Integrating between $r$ and $tr$ for each fixed $t&gt;0$ shows $m_2(tr)/m_2(r)\to t^{3\alpha}$; integrating from a fixed radius also gives $m_2(r)=r^{3\alpha+o(1)}$.</p>
<p>On the other hand, the assumed upper bound and hydrodynamics give $m_2(r)=o(r^{h+\alpha})$. This is impossible because $h+\alpha=(d+3\alpha)/2&lt;3\alpha$.</p>
<p>This argument uses a fixed $C$, not a scale factor tending to infinity with $r$. In applications, weak cutoff localization with a fixed error, such as $\varepsilon=1$, can suffice for constant-factor moment bounds. It must still be combined with rooted damping, monotone cutoff coupling and the model's differential error estimates. The theorem does not derive those estimates from (wCL) alone.</p>

## The interval estimate behind a stronger lower bound {#section-interval}

<a id="tag-DISO" data-assertion="proposition" data-title="A moment growing faster than its upper envelope cannot remain on a long interval"></a>
<p>Let $C\geq1$, $s&gt;0$, $R\geq Cs$, $B\geq b&gt;0$, and $\lambda&gt;k$. Let $f$ be positive and locally absolutely continuous on $[s,R/C]$. If</p>
<div class="math-display">$$f(s)\geq bs^k,\qquad f(R/C)\leq B(R/C)^k,\qquad (\log f)'(t)\geq\frac\lambda t\ \text{a.e.},$$</div>
<p>then $R/s\leq C(B/b)^{1/(\lambda-k)}$.</p>
<p><em>Proof.</em> Integration gives $f(R/C)\geq bs^k(R/(Cs))^\lambda$. Compare with the upper bound and divide by $b(R/C)^k$.</p>
<p>In the application, $k=\alpha+h$. At a scale with $M_s\geq\delta s^h$, the preceding quantile bound and $|B_s|\preceq s^d$ give $m_2(s)\succeq s^{3h-d}=s^k$. If a derivative lower bound with exponent $\lambda&gt;k$ holds throughout a subsequent interval of small quantiles, and $m_2(t)\preceq t^k$ holds at its far endpoint, the proposition bounds the interval's multiplicative length. These endpoint and derivative hypotheses are essential. Turning the subsequence conclusion into a lower bound at every large scale additionally requires controlling the intervals between good scales and monotonicity of the cutoff-window quantile. No such upgrade is inferred merely from the contradiction theorem.</p>

## Extending the lower bound to every large scale {#section-all-scales}

<a id="tag-YEVN" data-assertion="theorem" data-title="A last-good-scale argument gives a uniform quantile lower bound"></a>
<p>Let $d,h,r_0,c,B,\delta&gt;0$, $C\geq1$, and put $k=3h-d$. Let $M:[r_0,\infty)\to(0,\infty)$ be nondecreasing and let $f$ be positive and locally absolutely continuous. Suppose for every $r\geq r_0$,</p>
<div class="math-display">$$c\frac{M(r)^3}{r^d}\leq f(r)\leq Br^k.$$</div>
<p>Suppose also that for some $\lambda&gt;k$, almost every $r\geq r_0$ satisfies</p>
<div class="math-display">$$M(Cr)\leq\delta(Cr)^h\quad\Longrightarrow\quad(\log f)'(r)\geq\frac\lambda r.$$</div>
<p>If $M(r_*)\geq\delta r_*^h$ for some $r_*\geq r_0$, then, with</p>
<div class="math-display">$$L=C\left(\frac{B}{c\delta^3}\right)^{1/(\lambda-k)},$$</div>
<p>one has $L\geq C$ and $M(R)\geq\delta L^{-h}R^h$ for every $R\geq r_*$.</p>
<p><em>Proof.</em> The two bounds on $f(r_*)$ imply $B\geq c\delta^3$, so $L\geq C$. Fix $R\geq r_*$. Let $s$ be the supremum of the good scales in $[r_*,R]$, where a scale $u$ is good if $M(u)\geq\delta u^h$. Then $s$ is itself good. Indeed, either it is attained or there is a sequence of good scales increasing to it, and monotonicity gives $M(s)\geq\delta s^h$ by taking the limit. No continuity of the quantile function is required.</p>
<p>Every $u\in(s,R]$ is bad. If $R&lt;Cs$, then $R/s&lt;C\leq L$. Otherwise, for almost every $t\in(s,R/C)$ the scale $Ct$ is bad, so $(\log f)'(t)\geq\lambda/t$. Also $f(s)\geq c\delta^3s^k$ and $f(R/C)\leq B(R/C)^k$. The preceding interval estimate therefore gives $R/s\leq L$. In both cases, monotonicity yields $M(R)\geq M(s)\geq\delta s^h\geq\delta L^{-h}R^h$.</p>

<a id="tag-NS0Q" data-assertion="corollary" data-title="Conditional all-scale largest-cluster order from cutoff moment equations"></a>
<p>Under the hypotheses of <a href="/tag/XB1X/">the hydrodynamic contradiction theorem</a>, suppose additionally that $M$ is nondecreasing and, for some $c,U&gt;0$ and all sufficiently large $r$,</p>
<div class="math-display">$$m_2(r)\geq c\frac{M(r)^3}{r^d},\qquad M(r)\leq Ur^h,\qquad h=\frac{d+\alpha}{2}.$$</div>
<p>Then $M(r)\asymp r^h$ as $r\to\infty$.</p>
<p><em>Proof.</em> Put $k=\alpha+h=3h-d$. The assumed bound $m_2(r)\leq K M(Cr)m_1(r)$ and $m_1(r)\asymp r^\alpha$ give $m_2(r)\leq Br^k$ for some finite $B$. The first moment equation, $e_1\geq0$, and $m_1(r)\to\infty$ give</p>
<div class="math-display">$$\frac1{m_1(r)}=\int_r^\infty a(t)(1-e_1(t))\,dt\leq\int_r^\infty a(t)\,dt\sim\frac{a_0}{\alpha}r^{-\alpha}.$$</div>
<p>Consequently $\liminf_{r\to\infty}r a(r)m_1(r)\geq\alpha$. Choose $\eta\in(0,1)$ so small that $\lambda=3\alpha(1-\eta)^2&gt;k$, which is possible because $d&lt;3\alpha$. Beyond a fixed scale, $a(r)m_1(r)\geq\alpha(1-\eta)/r$. Choose $\delta&gt;0$ sufficiently small that $K\delta^2C^{2h}\leq\eta$. If $M(Cr)\leq\delta(Cr)^h$, the second error is at most $\eta$, and hence</p>
<div class="math-display">$$(\log m_2)'(r)=3a(r)m_1(r)(1-e_2(r))\geq\frac\lambda r\quad\text{a.e.}$$</div>
<p>The contradiction theorem gives $\limsup M(r)/r^h&gt;0$. Decrease $\delta$ if necessary to obtain a good scale beyond every fixed lower threshold. The last-good-scale theorem, applied to $f=m_2$, now supplies a uniform lower bound. The upper bound is an assumption.</p>
<p>For a transitive cutoff law and finite windows with $|B_r|\leq V_0r^d$, the <a href="/tag/LQ6Y/">quantile moment estimate</a> gives both additional moment comparisons: its $p=1$ case and $m_1(r)\preceq r^\alpha$ give $M_r\preceq r^h$, while its $p=2$ case gives $m_2(r)\geq M_r^3/(8eV_0r^d)$. An increasing coupling of the cutoff laws, together with increasing windows, makes $M_r$ nondecreasing. Thus these geometric inputs can be verified separately; the differential equations and their error bounds remain substantive hypotheses.</p>
<p>The analytic hypotheses are consistent. For any $d,\alpha&gt;0$ with $d&lt;3\alpha$, take $M(r)=r^h$, $m_1(r)=r^\alpha$, $m_2(r)=r^k$, $a(r)=\alpha r^{-\alpha-1}$, $e_1=0$ and $e_2=1-k/(3\alpha)$. They satisfy the hypotheses with $C=K=c=U=1$. This is a witness for the scalar equations, not a claim that these exact functions are moments of a percolation model.</p>

## Source scope {#section-source}

<p>The proof components above cover the analytic contradiction and finite-box estimates. The two-cluster differential identities and their error bounds remain model-specific inputs; neither a complete low-dimensional theorem nor a full critical volume-tail asymptotic is asserted here. Marginal logarithms also require separate estimates, beyond the definition of hydrodynamics.</p>

<p>Consider a full-model tail $n^{-(d-\alpha)/(d+\alpha)}$. As a two-sided estimate for an almost surely finite cluster, it requires $\alpha&lt;d$: if $\alpha&gt;d$ the lower bound eventually exceeds one, while if $\alpha=d$ it is bounded away from zero. Thus the decaying-tail interpretation below $3\alpha$ concerns $\alpha&lt;d&lt;3\alpha$, together with the additional localization hypotheses. This restriction is not supplied merely by $d&lt;3\alpha$.</p>

<p>The paper’s introduction to §II.1.2 explicitly includes $\alpha=d$ as a possible discontinuous endpoint under its localization hypothesis. That case is outside the finite-cluster, decaying-tail interpretation above; it is not ruled out by a fractional-tail argument.</p>


## Quantile regularity at the last good scale {#section-good-scales-source}

<p>The <a href="/coverage/sources/perclib-3978a2f-scales/">good-scale source</a> proves the last-scale step in <a href="/tag/YEVN/">YEVN</a> without continuity of $M$. If good radii $r_n$ approach their supremum $s$ from below, then $\delta r_n^h\leq M(r_n)\leq M(s)$; continuity of $r\mapsto r^h$ yields $\delta s^h\leq M(s)$. The derivative condition is used only after $s$; deleting the single endpoint causes no problem for an almost-everywhere bound.</p>
<p>The source also separates the analytic estimates from their probabilistic premises. Its version of <a href="/tag/BZDZ/">BZDZ</a> holds under any finite measure and proves integrability of the higher moment from the lower moment and the uniform tail estimate. Its persistence theorem does not need positive $d$ or a separate assumption $B&gt;0$: the first good scale and the two moment bounds force $B\geq c\delta^3&gt;0$. The spatial interpretation and the derivative estimate on bad scales remain model inputs.</p>


## Exact equations for a soft cutoff {#section-exact-cutoff-equations}

<a id="tag-GG8B" data-assertion="proposition" data-title="Mass transport reduces the soft-cutoff derivatives to two-cluster volume sums"></a>
<p>On $\mathbb Z^d$, give the bond of displacement $z\ne0$ opening probability $1-e^{-k_r(z)}$, for $r\geq r_0&gt;0$. Suppose $k_r(z)=k_r(-z)\geq0$ is nondecreasing and locally absolutely continuous in $r$, and</p>
<div class="math-display">$$\partial_r k_r(z)=c(r)\mathbf1_{\{z\in B_r\}}\quad\text{for almost every }r,$$</div>
<p>where $c\geq0$ is measurable and locally essentially bounded, $B_r=-B_r$ is finite and nonempty, and the union of the $B_r$ over each bounded parameter interval is finite. Assume $\chi_r=\mathbb E_r|K_0|&lt;\infty$ for every finite $r$. Put $X=|K_0|$ and $m_p(r)=\mathbb E_rX^p$. Then every $m_p$, for positive integer $p$, is finite and locally absolutely continuous, and almost everywhere</p>
<div class="math-display">$$m_p'(r)=c(r)\sum_{\ell=0}^{p-1}\binom p\ell
\mathbb E_r\left[X^{\ell+1}\sum_{y\in B_r}\mathbf1_{\{y\notin K_0\}}|K_y|^{p-\ell}\right].$$</div>
<p>In particular,</p>
<div class="math-display">$$m_1'=c(r)\mathbb E_r\left[X\sum_{y\in B_r}\mathbf1_{\{y\notin K_0\}}|K_y|\right],\qquad
m_2'=3c(r)\mathbb E_r\left[X^2\sum_{y\in B_r}\mathbf1_{\{y\notin K_0\}}|K_y|\right].$$</div>
<p><em>Proof.</em> Apply <a href="/tag/1K61/">the mixed-moment derivative theorem</a> with $p$ constant polynomial factors. On a compact interval $[a,b]$, the rate is bounded by a constant times the indicator of a finite displacement set, and finite susceptibility at $b$ supplies its unweighted two-point summability hypothesis. The theorem therefore gives the integral identity, local absolute continuity and absolute integrability of the derivative sums. The tree-graph moment bound gives finiteness of all volume moments.</p>
<p>In its derivative formula, opening an edge from $u\in K_0$ to $v\notin K_0$ contributes</p>
<div class="math-display">$$\sum_{\ell=0}^{p-1}\binom p\ell X^\ell |K_v|^{p-\ell}.$$</div>
<p>Translation invariance permits mass transport from the marked root to $u$. Explicitly, for any nonnegative translation-covariant function $H(u,\omega)$,</p>
<div class="math-display">$$\mathbb E\sum_{u\in K_0}H(u,\omega)
=\sum_u\mathbb E[\mathbf1_{\{0\in K_{-u}\}}H(0,\omega)]
=\mathbb E[XH(0,\omega)].$$</div>
<p>Use this with the sum over $v$ in each term; the cluster at $u$ is the root cluster on $u\in K_0$. The displacement becomes $y=v-u\in B_r$, producing the stated factor $X^{\ell+1}$.</p>
<p>For $p=2$, the two types of terms are $X|K_y|^2$ and $2X^2|K_y|$. Translation by $-y$, followed by replacing $y$ by $-y$ in the sum over the symmetric set $B_r$, exchanges the expectation of the first with that of $X^2|K_y|$, including the indicator that the clusters are distinct. This gives the coefficient three. The diagonal, if included in $B_r$, contributes zero.</p>
<p>The paper's cutoff has $c(r)=\beta_c|J'(r)|$. Its asymptotic normalization makes this rate locally bounded after a sufficiently large starting radius. Finiteness of the finite-cutoff susceptibility remains a prerequisite when applying this result to that model. The exact identity retains $|J'(r)|$; replacing it by its asymptotic power belongs to a subsequent estimate.</p>

## From localized moments to the differential errors {#section-localization-errors}

<a id="tag-A3G0" data-assertion="theorem" data-title="Weak localization and rooted damping supply the hydrodynamic error bounds"></a>
<p>Assume the cutoff family of <a href="/tag/GG8B/">GG8B</a>, with nested windows $B_r$ containing the origin. Suppose, for some $d,\alpha,b&gt;0$ and all sufficiently large $r$,</p>
<div class="math-display">$$|B_r|\asymp r^d,\qquad \chi_r\asymp r^\alpha,\qquad c(r)|B_r|\sim b r^{-\alpha-1}.$$</div>
<p>Let $M(r,R)$ and $M_r=M(r,r)$ be the largest-intersection quantiles defined above. Suppose a fixed $C\geq1$ gives</p>
<div class="math-display">$$m_j(r)\leq2\mathbb E_r|K_0\cap B_{Cr}|^j\qquad(j=2,3,4),$$</div>
<p>and suppose $Y_r=|K_0\cap B_{Cr}|$ obeys the rooted damping bound</p>
<div class="math-display">$$\mathbb P_r(Y_r\geq t M(r,Cr))\leq A e^{-b_0t}\mathbb P_r(Y_r\geq M(r,Cr))\qquad(t\geq1),$$</div>
<p>with fixed $A,b_0&gt;0$. Then there are measurable errors $e_1,e_2\in[0,1]$ such that, almost everywhere,</p>
<div class="math-display">$$\chi_r'=c(r)|B_r|\chi_r^2(1-e_1),\qquad
m_2'=3c(r)|B_r|\chi_rm_2(1-e_2),\qquad
e_i(r)\leq K\frac{M_{Cr}^2}{r^{d+\alpha}}.$$</div>
<p>Also $m_2(r)\leq K M_{Cr}\chi_r$. If $d&lt;3\alpha$, these hypotheses imply $M_r\asymp r^{(d+\alpha)/2}$ as $r\to\infty$.</p>
<p><em>Proof.</em> Set $v=|B_r|$, $Z=|K_0\cap B_r|$, and define</p>
<div class="math-display">$$1-e_1=\frac{\mathbb E_r[X\sum_{y\in B_r}\mathbf1_{\{y\notin K_0\}}|K_y|]}{v\chi_r^2},\qquad
1-e_2=\frac{\mathbb E_r[X^2\sum_{y\in B_r}\mathbf1_{\{y\notin K_0\}}|K_y|]}{v\chi_rm_2}.$$</div>
<p>The denominators are finite and positive. Apply <a href="/tag/1AC7/">the finite-cluster correlation bounds</a>, first to $F(K)=|K|$, $G(K)=|K|$, and then to $F(K)=|K|^2$, $G(K)=|K|$. Translation invariance makes the marginal moments independent of the root. Summation over $B_r$ gives</p>
<div class="math-display">$$0\leq e_1\leq\min\left\{1,\frac{\mathbb E_r[X^2Z]}{v\chi_r^2}\right\},\qquad
0\leq e_2\leq\min\left\{1,\frac{\mathbb E_r[X^3Z]}{v\chi_rm_2}\right\}.$$</div>
<p>All subtractions are finite: Hölder bounds the product expectations by the corresponding finite volume moments. The definitions and GG8B give the two exact equations.</p>
<p>The independent uniform-coordinate coupling makes the cutoff law increasing, so $M(r,Cr)\leq M_{Cr}$. Apply <a href="/tag/BZDZ/">the damping moment estimate</a> to $Y_r$, with moment pairs $(1,1),(1,2),(2,2)$. The three localization assumptions then yield</p>
<div class="math-display">$$m_2\leq K M_{Cr}\chi_r,\qquad
m_3\leq K M_{Cr}^2\chi_r,\qquad
m_4\leq K M_{Cr}^2m_2.$$</div>
<p>Here $Y_r\leq X$ bounds the lower local moments. Since $Z\leq X$, substituting these estimates in the error bounds gives $e_i\leq K M_{Cr}^2/(v\chi_r)\leq K M_{Cr}^2/r^{d+\alpha}$.</p>
<p>Measurability of the errors follows from their expectation formulas. One may realize all parameters by independent uniforms; the continuous intensity coordinates make the configuration jointly measurable in the parameter and the uniforms. Nested finite windows have measurable membership indicators, so integration preserves measurability.</p>
<p>For the final assertion put $h=(d+\alpha)/2$. The <a href="/tag/LQ6Y/">quantile lower moment bounds</a>, applied with $p=1,2$, give $M_r\leq U r^h$ and $m_2(r)\geq c_*M_r^3/r^d$. Nested windows and the increasing coupling make $M_r$ nondecreasing. We have now supplied all the assumptions of <a href="/tag/NS0Q/">the all-scale quantile theorem</a>, with coefficient $a(r)=c(r)|B_r|$. Its conclusion proves the claim.</p>
<p>The constants $C,A,b_0$ are fixed as $r$ varies. This argument needs only constant-factor localization of moments two through four; it does not require the higher-point inequality or the full correlation-length condition. The susceptibility estimate and rooted damping are still inputs. The latter is the universal-tightness input in the source, not a consequence of weak localization by itself.</p>


## Recovering rooted window moments {#section-window-scaling}

<a id="tag-AS7A" data-assertion="theorem" data-title="A largest-intersection lower scale and an averaged upper bound determine every rooted window moment"></a>
<p>Let $(\mathbb P_r)_{r\geq r_0}$ be increasing translation-invariant independent-bond laws on $\mathbb Z^d$, dominated by a translation-invariant independent-bond law $\mathbb P_\infty$. Put $B_R=\{x:\|x\|_\infty\leq R\}$, $h=(d+\alpha)/2$ with $0&lt;\alpha\leq d$, and let $M_r$ be the largest-intersection quantile for law $r$ in window $B_r$. Suppose, for all sufficiently large $r$,</p>
<div class="math-display">$$M_r\geq c r^h,\qquad \mathbb E_\infty|K_0\cap B_r|\leq A r^\alpha,$$</div>
<p>where $c,A&gt;0$. Then for every integer $p\geq1$,</p>
<div class="math-display">$$\mathbb E_r|K_0\cap B_r|^p\asymp_p
\mathbb E_\infty|K_0\cap B_r|^p\asymp_p r^{\alpha+(p-1)h}.$$</div>
<p>If $m_p(r)=\mathbb E_r|K_0|^p$ additionally satisfies $m_p(r)\leq L_p\mathbb E_r|K_0\cap B_{C_pr}|^p$ for fixed finite $L_p,C_p\geq1$, then $m_p(r)$ has the same order. This last conclusion applies only to the orders for which localization is assumed.</p>
<p><em>Proof.</em> Denote the full-law quantile in $B_r$ by $M_r^*$. Partition counting and quantile minimality give</p>
<div class="math-display">$$\frac{(M_r^*)^2}{4e}\leq\sum_{x\in B_r}\mathbb E_\infty|K_x\cap B_r|
\leq |B_r|\mathbb E_\infty|K_0\cap B_{2r}|\leq C r^{d+\alpha}.$$</div>
<p>For the middle inequality translate $x$ to zero and use $B_r-x\subseteq B_{2r}$. Thus $M_r^*\leq C r^h$. The <a href="/articles/window-tightness-interfaces/#section-numerical-source">universal rooted tail bound</a> applies directly to the full independent-bond law, even if it has infinite clusters. Combining it with <a href="/tag/BZDZ/">the damping moment estimate</a> gives, for $p\geq2$,</p>
<div class="math-display">$$\mathbb E_\infty|K_0\cap B_r|^p
\leq C_p(M_r^*)^{p-1}\mathbb E_\infty|K_0\cap B_r|
\leq C_p r^{\alpha+(p-1)h}.$$</div>
<p>The case $p=1$ is the assumed averaged bound. Coupling gives the same upper bound for the cutoff law. It is the full-law quantile $M_r^*$ that is used in this application of damping; no equality with the cutoff quantile is assumed.</p>
<p>For the lower bound put $s=r/2$ and apply <a href="/tag/LQ6Y/">partition counting</a> under law $s$ in $B_s$. Translation and then the increasing coupling give</p>
<div class="math-display">$$\frac{M_s^{p+1}}{e\,2^{p+1}}
\leq\sum_{x\in B_s}\mathbb E_s|K_x\cap B_s|^p
\leq |B_s|\mathbb E_s|K_0\cap B_r|^p
\leq |B_s|\mathbb E_r|K_0\cap B_r|^p.$$</div>
<p>Since $M_s\geq c s^h$ and $|B_s|=O(s^d)$, division gives the lower power $r^{(p+1)h-d}=r^{\alpha+(p-1)h}$. Coupling transfers it to the full law. For the last assertion, the local count is at most the full cutoff cluster size, while the assumed localization and domination bound that size moment above by $L_p\mathbb E_\infty|K_0\cap B_{C_pr}|^p$. The fixed dilation changes only the constant.</p>
<p>This proves the geometric step in Corollary II.4.12. For $\alpha=d$ the power is $dp$, which is consistent with a positive-density contribution from infinite full-law clusters; full cutoff moments remain finite under their localization hypotheses.</p>

## How the source arguments fit together {#section-source-assembly}

<p>The general countable hierarchy <a href="/tag/09EI/">09EI</a>, its second-moment specialization <a href="/tag/6H7C/">6H7C</a>, the deficits <a href="/tag/NJF3/">NJF3</a> and the localized ratios <a href="/tag/0WAE/">0WAE</a> already provide the analytic ingredients of the power-law criterion <a href="/tag/YJ5E/">YJ5E</a>. GG8B and A3G0 display their application to the source's more general uniform-rate cutoff and retain the exact kernel derivative. They are not a replacement hierarchy.</p>
<p>The rooted damping used in those conditional statements is available for independent bonds from the <a href="/articles/window-tightness-interfaces/#section-source-proof">finite-witness amplification proof</a> and its <a href="/articles/window-tightness-interfaces/#section-numerical-source">numerical consequence</a>. They apply for any cutoff and observation radius separately, and to the full law. No restriction requiring the observation radius to exceed the cutoff radius is needed.</p>
<p>Consequently, for a cutoff meeting GG8B's regularity hypotheses, divergent cutoff susceptibility, the averaged full-law bound and weak localization of moments one through four suffice to apply <a href="/tag/79SD/">79SD</a>, then A3G0 when $d&lt;3\alpha$, and finally AS7A. This establishes susceptibility order, all-scale quantile order and every fixed window moment; it establishes full cutoff moments only through order four. The averaged bound, divergence and weak localization themselves still need verification for the model. A full volume-tail estimate additionally uses the mesoscopic and ghost-comparison arguments.</p>


## A moment alternative on many scales {#section-good-scale-alternative}

<p>Part III approaches critical-dimensional hydrodynamics along $\beta(r,\lambda)=\beta_c(1-\lambda r^{-\alpha})$, where $0&lt;\lambda\leq1$ is fixed while $r$ grows. Both the cutoff and the intensity increase. The first step finds many intervals on which either the second moment is large or the third moment is controlled. The following statement isolates that step from its probabilistic inputs.</p>
<a id="tag-X57A" data-assertion="theorem" data-title="A capped-moment estimate gives a positive-density moment alternative"></a>
<p>Fix $d\geq3\alpha&gt;0$ and put $h=(d+\alpha)/2$. Let $(T_r)_{r\geq1}$ be stochastically nondecreasing random variables with $T_r\geq1$. Write $m_p(r)=\mathbb E T_r^p$ and $\chi=m_1$. Assume that the first three moments are finite, have polynomial upper bounds, and satisfy</p>
<div class="math-display">$$m_2(r)\leq\chi(r)^3,\qquad m_3(r)\leq C_T\chi(r)^2m_2(r).$$</div>
<p>Suppose also that there are $\delta&gt;0$, $0&lt;c\leq1$ and $C_I&lt;\infty$ such that, for all sufficiently large arguments,</p>
<div class="math-display">$$\chi(2r)\geq(1+\delta)\chi(r),\qquad
\int_u^v s^{-\alpha-1}\mathbb E\min(T_s,cs^h)\,ds
\leq C_I\log\frac{\chi(v)}{\chi(u)}\quad(v\geq u).$$</div>
<p>Then there are $a,A&gt;0$ and a set $\mathcal K$ of positive integers of lower density at least $1/2$ such that each $k\in\mathcal K$ has one of the following properties throughout $[2^k,2^{k+2}]$:</p>
<div class="math-display">$$m_2(r)\geq a\chi(r)^3\quad\text{for every }r,
\qquad\text{or}\qquad
m_3(r)\leq A r^{d+\alpha}\chi(r)\quad\text{for every }r.$$</div>
<p>The choice of alternative is for the whole interval. Constants are uniform over families with common input constants and common polynomial exponents.</p>
<p><em>Proof.</em> Define the nondecreasing comparison radius</p>
<div class="math-display">$$R(r)=\left(\frac2c\sqrt{\chi(r)m_2(r)}\right)^{1/h}.$$</div>
<p>Under size bias by $T_r$, its mean is $m_2(r)/\chi(r)\leq\sqrt{\chi(r)m_2(r)}$. Markov's inequality consequently leaves at least half of the first moment below $2\sqrt{\chi(r)m_2(r)}$. Increasing the truncation to a cap gives</p>
<div class="math-display">$$\chi(r)\leq2\mathbb E\min(T_r,cR(r)^h).$$</div>
<p>Also, since $m_2$ is nondecreasing,</p>
<div class="math-display">$$R(2r)\geq(1+\delta)^{1/(d+\alpha)}R(r)=:(1+\eta)R(r)$$</div>
<p>for all large $r$. In particular $R(r)\to\infty$, so the assumed integral estimate eventually applies at this radius.</p>
<p>We need simultaneous doubling for the four positive nondecreasing functions $\chi(r)$, $R(r)$, $\chi(R(r))$ and $m_3(r)$. Each has a polynomial upper bound. For any positive nondecreasing $f$ with $f(r)\leq B r^b$, let a dyadic index be bad if $f(4r)&gt;L f(r)$ for some $r\in[2^k,2^{k+2}]$. Then</p>
<div class="math-display">$$\log f(2^{k+4})-\log f(2^k)&gt;\log L.$$</div>
<p>All these differences are nonnegative. Summing through $N$ telescopes in the four residue classes modulo four, giving a total at most $4bN\log2+O(1)$. Hence the upper density of bad indices is at most $4b\log2/\log L$. Choose $L&gt;1$ so large that the sum of these bounds for the four functions is less than $1/2$. Outside their union of bad indices, each function satisfies $f(4r)\leq Lf(r)$ throughout the required interval. Removing finitely many small indices leaves a set $\mathcal K$ of lower density at least $1/2$.</p>
<p>Fix a good $k$ and $r\in[2^k,2^{k+2}]$, and put $u=R(r)$. Doubling of the composed function and reverse doubling of $R$ imply</p>
<div class="math-display">$$\chi((1+\eta)u)\leq\chi(R(2r))\leq L\chi(u).$$</div>
<p>The function $s\mapsto\mathbb E\min(T_s,cs^h)$ is nondecreasing. The integral hypothesis therefore gives</p>
<div class="math-display">$$\frac{1-(1+\eta)^{-\alpha}}{\alpha}\,u^{-\alpha}\mathbb E\min(T_u,cu^h)
\leq\int_u^{(1+\eta)u}s^{-\alpha-1}\mathbb E\min(T_s,cs^h)\,ds
\leq C_I\log L.$$</div>
<p>Thus $\mathbb E\min(T_{R(r)},cR(r)^h)\leq C R(r)^\alpha$, uniformly throughout each good interval.</p>
<p>If $R(2^k)\geq2^{k+2}$, then $R(r)\geq r$ throughout that interval. Stochastic monotonicity and the cap bound yield $\chi(r)\leq C R(r)^\alpha$. Substitute the definition of $R$ and raise to the power $(d+\alpha)/\alpha$ to obtain</p>
<div class="math-display">$$m_2(r)\geq c_0\chi(r)^{d/\alpha}\geq c_0\chi(r)^3.$$</div>
<p>The last inequality uses $d\geq3\alpha$ and $\chi\geq1$. This is the first alternative.</p>
<p>Otherwise $R(2^k)&lt;2^{k+2}$. Doubling of $R$ at $2^k$ gives, for every $r$ in the same interval, $R(r)\leq R(2^{k+2})\leq L R(2^k)&lt;4Lr$. Hence $\chi(r)m_2(r)=(c^2/4)R(r)^{d+\alpha}\leq C r^{d+\alpha}$. The mixed tree bound then gives $m_3(r)\leq C_T\chi(r)^2m_2(r)\leq C r^{d+\alpha}\chi(r)$, the second alternative.</p>
<p>This is the mechanism of Lemma III.3.11. Polynomial growth produces many common doubling intervals, not doubling at every scale. No monotonicity of the ratio $m_2/\chi$ was used: the radius is built from the product $\chi m_2$ for precisely this reason. The reverse-doubling and integrated capped-moment bounds remain explicit inputs, and the statement is used only at sufficiently large radii.</p>

## Bounding susceptibility on a good interval {#section-good-scale-susceptibility}

<a id="tag-1BO9" data-assertion="proposition" data-title="The moment alternative and two derivative bounds control susceptibility on good intervals"></a>
<p>Retain X57A and suppose $\chi$ is locally absolutely continuous. For a fixed $0&lt;\lambda\leq1$, assume constants $a_1,a_2&gt;0$ and $b_1,b_2\geq0$ give, almost everywhere at sufficiently large $r$,</p>
<div class="math-display">$$\begin{aligned}
\chi'(r)&\geq\lambda r^{-\alpha-1}\left(a_1\frac{m_2(r)}{\chi(r)}-b_1\chi(r)\right),\\
\chi'(r)&\geq r^{-\alpha-1}\left(a_2\chi(r)^2-b_2r^{-d}m_3(r)\right).
\end{aligned}$$</div>
<p>Then, for a constant $C$ depending only on these constants and those of X57A, every sufficiently large $k\in\mathcal K$ satisfies</p>
<div class="math-display">$$\chi(r)\leq C\lambda^{-1}r^\alpha\qquad(2^k\leq r\leq2^{k+1}).$$</div>
<p>On intervals satisfying the bound on $m_3$, the stronger estimate $\chi(r)\leq C r^\alpha$ holds.</p>
<p><em>Proof.</em> On a first-alternative interval, the first derivative bound becomes</p>
<div class="math-display">$$\chi'(s)\geq\lambda s^{-\alpha-1}\left(a_1a\chi(s)^2-b_1\chi(s)\right).$$</div>
<p>On a second-alternative interval, the second derivative bound becomes</p>
<div class="math-display">$$\chi'(s)\geq s^{-\alpha-1}\left(a_2\chi(s)^2-b_2A s^\alpha\chi(s)\right).$$</div>
<p>Choose $K\geq1$ large enough to absorb the linear term in either case whenever $\chi(s)\geq K s^\alpha$. Above this threshold, both alternatives give $\chi'(s)\geq c\lambda s^{-\alpha-1}\chi(s)^2$, with the factor $\lambda$ unnecessary in the second case.</p>
<p>Fix $r\in[2^k,2^{k+1}]$. If $\chi(r)&lt;K(2r)^\alpha$, the desired bound already holds. Otherwise monotonicity gives $\chi(s)\geq\chi(r)\geq K(2r)^\alpha\geq Ks^\alpha$ throughout $[r,2r]$. This interval is contained in $[2^k,2^{k+2}]$, where a single alternative applies. Since $\chi$ is positive and locally absolutely continuous, integration of its reciprocal gives</p>
<div class="math-display">$$\frac1{\chi(r)}=\frac1{\chi(2r)}+\int_r^{2r}\frac{\chi'(s)}{\chi(s)^2}\,ds
\geq\frac{c\lambda(1-2^{-\alpha})}{\alpha}\,r^{-\alpha}.$$</div>
<p>Taking reciprocals proves the claim. In the second case the same calculation omits $\lambda$. This argument retains the lower-order terms until the threshold has been met; it does not assume a quadratic derivative lower bound when susceptibility is already small.</p>
<p>For the modified cutoff family in Part III, the two premises come from the intensity derivative lower bound and the spatial-cutoff derivative lower bound, respectively. The chain rule uses</p>
<div class="math-display">$$\frac{d}{dr}\beta(r,\lambda)=\alpha\lambda\beta_c r^{-\alpha-1},$$</div>
<p>so its positive intensity contribution cannot be discarded in the first alternative. With the source inputs verified uniformly in $\lambda$, this gives the conclusion of Lemma III.3.4. It proves an unbounded supply of good intervals, not the all-scale estimates of section III.3.2 or hydrodynamics itself. The conjectured comparison of the two derivatives in Remark III.3.3 is not used.</p>


## Comparing the modified and critical intensities {#section-modified-reciprocal}

<a id="tag-AGX4" data-assertion="proposition" data-title="Reciprocal transport between the modified and critical cutoff laws"></a>
<p>Let $\alpha,b,M&gt;0$ and $F:[1,\infty)\times[0,b]\to(0,\infty)$. Suppose $F(r,\cdot)$ is absolutely continuous and $0\leq\partial_\beta F(r,\beta)\leq M F(r,\beta)^2$ almost everywhere, for every fixed $r$. Put</p>
<div class="math-display">$$\chi_\lambda(r)=F(r,b(1-\lambda r^{-\alpha}))\qquad(0\leq\lambda\leq1).$$</div>
<p>For every $r\geq1$ and $0\leq\lambda\leq1$,</p>
<div class="math-display">$$\frac1{\chi_\lambda(r)}\leq\frac1{\chi_0(r)}+\lambda bM r^{-\alpha}.$$</div>
<p>If $\chi_0(r)/r^\alpha\to\infty$, then, for each fixed $0&lt;\lambda\leq1$,</p>
<div class="math-display">$$\liminf_{r\to\infty}\frac{\chi_\lambda(r)}{r^\alpha}\geq\frac1{\lambda bM}.$$</div>
<p>Consequently, suppose a constant $C&gt;0$, independent of $\lambda$, bounds $\chi_\lambda(2^k)\leq C2^{k\alpha}$ on a set $\mathcal K_{2,\lambda}$ for each $0\leq\lambda\leq1$. Then $\mathcal K_{2,\lambda}$ is finite for every $0\leq\lambda\leq\min\{1,(2bMC)^{-1}\}$.</p>
<p><em>Proof.</em> For fixed $r$, the positive continuous function $F(r,\cdot)$ has a positive minimum on $[0,b]$. Its reciprocal is absolutely continuous, with derivative $-\partial_\beta F/F^2$. Writing $\beta_\lambda=b(1-\lambda r^{-\alpha})$ gives</p>
<div class="math-display">$$\frac1{\chi_0(r)}
=\frac1{\chi_\lambda(r)}-\int_{\beta_\lambda}^b
\frac{\partial_\beta F(r,\beta)}{F(r,\beta)^2}\,d\beta
\geq\frac1{\chi_\lambda(r)}-M(b-\beta_\lambda).$$</div>
<p>Rearrange and use $b-\beta_\lambda=\lambda b r^{-\alpha}$. Multiplication by $r^\alpha$ and the assumed divergence give $\limsup r^\alpha/\chi_\lambda(r)\leq\lambda bM$, proving the lower bound. For the final assertion and positive $\lambda$ in the stated range, this lower limit is at least $2C$, incompatible with infinitely many values bounded above by $C$. For $\lambda=0$, use the assumed divergence directly.</p>
<p>In Part III, take $F(r,\beta)=\mathbb E_{\beta,r}|K_o|$, $b=\beta_c$ and $M=|J|$. The derivative upper bound and finite cutoff susceptibility are model inputs. The third-moment intervals in 1BO9 provide the constant $C$ when their hypotheses hold uniformly; its second-case proof also works at $\lambda=0$. This supplies the reciprocal implication and finiteness argument in Corollary III.3.12. The assumption that critical cutoff susceptibility divided by $r^\alpha$ diverges is a premise of this implication, not a newly established fact about the model.</p>
<p>Two <a href="/errata/hutchcroft-lrp-3/">provisional source entries</a> record the missing factor $\alpha$ in the preceding modified-intensity chain rule and the missing square and incorrect integration variable in this reciprocal calculation. The corrected formulas retain the source conclusions; their status awaits Tom's confirmation.</p>


## Polynomial moments for the radial cutoff {#section-polynomial-cutoff}

<a id="tag-DR1W" data-assertion="theorem" data-title="Critical radial soft cutoffs have polynomially bounded moments"></a>
<p>Let $d\geq1$ be an integer, $0&lt;\alpha&lt;d$, and fix a norm on $\mathbb R^d$. Let $j:(0,\infty)\to(0,\infty)$ be nonincreasing and satisfy $j(t)\sim a t^{-d-\alpha}$ for some $a&gt;0$. On distinct vertices of $\mathbb Z^d$, put</p>
<div class="math-display">$$J(x,y)=j(\|x-y\|),\qquad J_r(x,y)=(J(x,y)-j(r))_+.$$</div>
<p>Let $\beta_c$ be the full model's critical intensity. For each integer $p\geq1$, the cutoff moment $m_p(\beta,r)=\mathbb E_{\beta,r}|K_o|^p$ is finite for every finite $r&gt;0$ and $0\leq\beta\leq\beta_c$. Moreover, for $r\geq1$,</p>
<div class="math-display">$$m_p(\beta,r)\leq C_p(1+r)^{(2p-1)(d+\alpha)(d+2\alpha)/(d-\alpha)}.$$</div>
<p>The constant is uniform in $\beta$. In particular it applies to every modified law $\beta=\beta_c(1-\lambda r^{-\alpha})$ with $r\geq1$ and $0\leq\lambda\leq1$.</p>
<p><em>Proof.</em> Norm equivalence and the asymptotic for $j$ give a summable kernel with the power-law lower envelope of <a href="/tag/KXV3/">KXV3</a>. That theorem supplies $0&lt;\beta_c&lt;\infty$ and a critical volume-tail bound of exponent $\theta=(d-\alpha)/(2d+\alpha)$. Applying <a href="/tag/I328/">polynomial tail transfer</a> gives</p>
<div class="math-display">$$\chi_\beta\leq C(\beta_c-\beta)^{-\gamma},\qquad\gamma=\frac{d+2\alpha}{d-\alpha},\qquad 0\leq\beta&lt;\beta_c.$$</div>
<p>The positive lattice distances have a minimum, so $J_*:=\max_{z\ne0}j(\|z\|)$ is finite and positive. If $j(r)\geq J_*$, the cutoff has no positive bonds. Otherwise, writing $q=j(r)/J_*\in(0,1)$, one has</p>
<div class="math-display">$$(J(x,y)-j(r))_+\leq(1-q)J(x,y).$$</div>
<p>For a positive left side this is just $J(x,y)\leq J_*$; for a zero left side it is immediate. Hence the critical cutoff is dominated by the full model at intensity $\beta_c(1-q)&lt;\beta_c$. Its susceptibility is finite and at most $C(\beta_c q)^{-\gamma}$. Since $j(r)\geq c(1+r)^{-d-\alpha}$ for $r\geq1$, this is at most $C'(1+r)^{(d+\alpha)\gamma}$. Finally <a href="/tag/Y84V/">the tree-graph moment bound</a> gives $m_p\leq(2p-3)!!\chi^{2p-1}$. Domination proves the same estimates below critical intensity.</p>
<p>This supplies Lemma III.3.5 from the critical-tail theorem and the ghost derivative inequality already treated in the wiki. It does not use the sharper critical window estimate needed below.</p>

## A capped lower bound for the cutoff derivative {#section-capped-cutoff-derivative}

<a id="tag-KPBJ" data-assertion="proposition" data-title="A critical window bound controls the cutoff derivative error"></a>
<p>Retain the radial model of DR1W and assume also that $j$ is continuously differentiable. Write $B_r=\{z\in\mathbb Z^d:0&lt;\|z\|\leq r\}$. Suppose that, for some $A&lt;\infty$ and all sufficiently large $r$, the full critical law satisfies</p>
<div class="math-display">$$\mathbb E_{\beta_c}|K_o\cap B_r|\leq A r^\alpha.$$</div>
<p>There is $C&lt;\infty$ such that, for each fixed $0&lt;\beta\leq\beta_c$ and almost every sufficiently large $r$,</p>
<div class="math-display">$$\partial_r\chi(\beta,r)\geq\beta|j'(r)|\,|B_r|\,\chi(\beta,r)
\left(\mathbb E_{\beta,r}\min\{|K_o|,m\}-C m r^{-(d-\alpha)/2}\right)\qquad(m\geq1).$$</div>
<p><em>Proof.</em> The cutoff moments are finite by DR1W. On a compact radius interval they are dominated by those at its upper endpoint, while the derivative kernels have uniformly bounded finite support in displacement. The <a href="/tag/GG8B/">cutoff identity</a> therefore applies: with $X=|K_o|$ and $Y_y=|K_y|$,</p>
<div class="math-display">$$\partial_r\chi=\beta|j'(r)|\mathbb E\left[X\sum_{y\in B_r}Y_y\mathbf1_{\{o\nleftrightarrow y\}}\right].$$</div>
<p>Replace $Y_y$ by $Y_y\wedge m$. Harris gives $\mathbb E[X(Y_y\wedge m)]\geq\chi\mathbb E(X\wedge m)$. On $\{o\leftrightarrow y\}$, the two clusters agree. Subtracting these terms gives</p>
<div class="math-display">$$\partial_r\chi\geq\beta|j'(r)|\left[|B_r|\chi\mathbb E(X\wedge m)-m\mathbb E[X|K_o\cap B_r|]\right].$$</div>
<p>By <a href="/tag/BIXQ/">the mixed window bound</a> and domination by the full critical law, the last expectation is at most $\sqrt8\chi\sqrt{|B_r|A r^\alpha}$. Since $|B_r|\geq c r^d$ at large radii, this proves the claim. The radius identity is valid outside a common null set, and the remaining inequalities hold for every cap $m$, so the estimate also permits a cap chosen as a function of $r$.</p>
<p>The sharp window hypothesis is distinct from the weaker averaged estimate in KXV3. Together with the cited Gladkov three-point theorem, it is an explicit input to this version of Lemma III.3.6.</p>

## The modified susceptibility grows at least as a power {#section-modified-lower}

<a id="tag-C0OR" data-assertion="proposition" data-title="Reciprocal integration gives a uniform lower bound for the modified susceptibility"></a>
<p>Retain DR1W, assume $j$ is continuously differentiable with $|j'(r)|\sim r^{-d-\alpha-1}$, and normalize the norm so that its unit ball has Lebesgue volume one. Put $M=\sum_{z\ne0}J(0,z)$ and, for $r\geq1$,</p>
<div class="math-display">$$\beta_\lambda(r)=\beta_c(1-\lambda r^{-\alpha}),\qquad
\widetilde\chi_\lambda(r)=\chi(\beta_\lambda(r),r),\qquad0\leq\lambda\leq1.$$</div>
<p>For each fixed $\lambda$,</p>
<div class="math-display">$$\liminf_{r\to\infty}r^{-\alpha}\widetilde\chi_\lambda(r)
\geq\frac{\alpha}{\beta_c(1+\alpha\lambda M)}.$$</div>
<p>There are also $c&gt;0$ and $R_0&lt;\infty$, independent of $\lambda$, such that $\widetilde\chi_\lambda(r)\geq c r^\alpha$ for all $r\geq R_0$.</p>
<p><em>Proof.</em> The increasing one-parameter kernel $\beta_\lambda(r)J_r$ has, almost everywhere, rate</p>
<div class="math-display">$$\dot k_r(z)=\beta_\lambda(r)|j'(r)|\mathbf1_{B_r}(z)
+\alpha\lambda\beta_c r^{-\alpha-1}J_r(0,z).$$</div>
<p>On compact radius intervals these rates have bounded displacement support and bounded row sums, and the upper-endpoint critical cutoff dominates all cluster moments. The finite-volume integrated Russo argument for GG8B thus applies to this path as well. Passing to the limit using the BK bound for two distinct clusters gives local absolute continuity and</p>
<div class="math-display">$$0\leq\widetilde\chi_\lambda'(r)\leq
\beta_c\left(|j'(r)||B_r|+\alpha\lambda M r^{-\alpha-1}\right)\widetilde\chi_\lambda(r)^2.$$</div>
<p>This derivation uses the derivative of the whole kernel, so both increasing contributions are retained; it needs no unproved joint differentiability assertion in the two parameters.</p>
<p>The full critical susceptibility is infinite. Otherwise <a href="/tag/5LNL/">right-openness</a> would give finite susceptibility, and hence no infinite cluster, at some intensity above $\beta_c$. Finite path witnesses and monotone convergence imply $\widetilde\chi_\lambda(r)\uparrow\chi_{\beta_c}=\infty$. Integrating the reciprocal to infinity therefore gives</p>
<div class="math-display">$$\frac1{\widetilde\chi_\lambda(r)}\leq\beta_c\int_r^\infty
\left(|j'(s)||B_s|+\alpha\lambda M s^{-\alpha-1}\right)\,ds
\sim\frac{\beta_c(1+\alpha\lambda M)}{\alpha}r^{-\alpha}.$$</div>
<p>Here $|B_s|\sim s^d$ by the normalization of the norm; lattice-point counting follows by comparing the union of unit cubes centered at these points with norm balls of radii $s+O(1)$ and $s-O(1)$. Taking reciprocals proves the first claim. Bounding $\lambda$ by one in the same integral gives the second with a common radius and constant. This proves Lemma III.3.8 without the critical window hypothesis.</p>

## Reverse doubling and the capped integral {#section-model-reverse-doubling}

<a id="tag-N3OC" data-assertion="theorem" data-title="The critical window estimate gives eventual uniform reverse doubling"></a>
<p>Assume the radial hypotheses of C0OR, the critical window bound of KPBJ, and $d\geq3\alpha$. Write $h=(d+\alpha)/2$ and let $\widetilde T_{r,\lambda}$ be the cluster volume in the modified law. There are $a,b,\eta&gt;0$, $c\in(0,1]$ and $R_1&lt;\infty$, independent of $\lambda\in[0,1]$, such that</p>
<div class="math-display">$$\frac{d}{dr}\log\widetilde\chi_\lambda(r)
\geq a r^{-\alpha-1}\mathbb E\min\{\widetilde T_{r,\lambda},c r^h\}
\geq\frac b r\quad\text{for almost every }r\geq R_1.$$</div>
<p>Consequently, for $v\geq u\geq R_1$,</p>
<div class="math-display">$$\widetilde\chi_\lambda(2u)\geq(1+\eta)\widetilde\chi_\lambda(u),\qquad
\int_u^v r^{-\alpha-1}\mathbb E\min\{\widetilde T_{r,\lambda},c r^h\}\,dr
\leq a^{-1}\log\frac{\widetilde\chi_\lambda(v)}{\widetilde\chi_\lambda(u)}.$$</div>
<p><em>Proof.</em> C0OR gives $\widetilde\chi_\lambda(r)\geq c_0r^\alpha$ uniformly at large radii. Since $h\geq2\alpha$, <a href="/tag/XU1Y/">the universal cap bound</a> implies, for $0&lt;\delta\leq1$ and $\delta r^{2\alpha}\geq1$,</p>
<div class="math-display">$$\mathbb E\min\{\widetilde T_{r,\lambda},\delta r^h\}
\geq\tfrac12\min\{c_0,\sqrt{\delta/2}\}\,r^\alpha
\geq c_1\sqrt\delta\,r^\alpha,$$</div>
<p>where $c_1=\tfrac12\min\{c_0,1/\sqrt2\}$. Choose a fixed $c=\delta\in(0,1]$ sufficiently small that $C\delta\leq c_1\sqrt\delta/2$, with $C$ from KPBJ. Its error at cap $\delta r^h$ is $C\delta r^\alpha$, at most half the capped mean.</p>
<p>At sufficiently large radii, uniformly in $\lambda$, one has $\beta_\lambda(r)\geq\beta_c/2$ and $\beta_\lambda(r)|j'(r)||B_r|\geq c_2 r^{-\alpha-1}$. In the Russo identity for the modified path, discard only the nonnegative intensity-rate contribution. The cutoff contribution, estimated exactly as in KPBJ at the current law, gives</p>
<div class="math-display">$$\frac{\widetilde\chi_\lambda'}{\widetilde\chi_\lambda}
\geq\tfrac12 c_2r^{-\alpha-1}\mathbb E\min\{\widetilde T_{r,\lambda},\delta r^h\}
\geq\tfrac12 c_2c_1\sqrt\delta\,r^{-1}.$$</div>
<p>Integrate the first inequality on $[u,v]$ for the capped integral, and the second on $[u,2u]$ for reverse doubling, taking $1+\eta=2^b$. All thresholds are independent of $\lambda$.</p>
<p>This gives the large-radius conclusions of Lemma III.3.9 and Corollary III.3.10 in the range $d\geq3\alpha$, including equality. It does not extend the derivative estimate to every $r\geq1$, nor to the larger range $\alpha&lt;d$ printed in the corollary.</p>

## Applying the good-scale alternative to the model {#section-model-good-scales}

<a id="tag-X8F6" data-assertion="corollary" data-title="Conditional good-scale susceptibility bound for the radial model"></a>
<p>Under the hypotheses of N3OC, there is $C&lt;\infty$, independent of $0&lt;\lambda\leq1$, such that for each such $\lambda$ there is a set $\mathcal K_\lambda$ of integers of lower density at least one half with</p>
<div class="math-display">$$\widetilde\chi_\lambda(r)\leq C\lambda^{-1}r^\alpha\qquad\left(2^k\leq r\leq2^{k+1},\ k\in\mathcal K_\lambda\text{ sufficiently large}\right).$$</div>
<p>This is conditional on the critical window bound and on the finite Gladkov theorem used by 87RB.</p>

<p>The preceding results discharge the model premises of <a href="/tag/X57A/">the good-scale alternative</a>, subject to the critical window estimate and the cited finite Gladkov theorem. Indeed, DR1W supplies polynomial moments uniformly in $\lambda$; Y84V and <a href="/tag/9WYX/">9WYX</a> give $m_2\leq\chi^3$ and $m_3\leq3\chi^2m_2$; N3OC gives the common reverse-doubling and capped-integral constants. Both the cutoff and its modified intensity increase, as required for the stochastic monotonicity premise. Thus the moment alternatives hold on a set of dyadic intervals of lower density at least one half for each $\lambda$.</p>
<p>For completeness, the two derivative premises of <a href="/tag/1BO9/">the good-interval susceptibility bound</a> also follow in this model. The cutoff contribution and Harris give directly</p>
<div class="math-display">$$\partial_r\chi(\beta,r)\geq\beta|j'(r)|\left(|B_r|\chi(\beta,r)^2-m_3(\beta,r)\right):$$</div>
<p>the subtracted term is $\mathbb E[|K_o|^2|K_o\cap B_r|]\leq m_3$. For the intensity contribution, <a href="/tag/VW2E/">the second-moment derivative bound</a> and $\beta_\lambda'(r)=\alpha\lambda\beta_c r^{-\alpha-1}$ give a lower bound of the form $\lambda r^{-\alpha-1}(a_1m_2/\chi-b_1\chi)$, uniformly when $\beta_\lambda(r)\geq\beta_c/2$. These estimates hold along the modified path by its integrated Russo formula; equivalently, the intensity derivative inequality extends from almost every intensity to every positive finite-susceptibility intensity by continuity. The pivotal rate is continuous by NMYK, and the second moment is continuous by domination under a common nearby finite-susceptibility law, as in <a href="/tag/IK5Y/">IK5Y</a>. Right-openness supplies that law for each fixed cutoff.</p>
<p>Since $|j'(r)||B_r|\asymp r^{-\alpha-1}$ and $|j'(r)|\asymp r^{-d-\alpha-1}$, these are precisely the two inequalities of 1BO9, with constants independent of $\lambda$. Hence, for $0&lt;\lambda\leq1$, the modified susceptibility is at most $C\lambda^{-1}r^\alpha$ on the lower halves of the selected intervals. In particular this gives the conditional model proof of Lemma III.3.4 at $d=3\alpha$. No comparison between the two derivatives from the source's conjecture is assumed. The sharper spatial-window input and the finite Gladkov theorem are still separate proof obligations; all-scale fictitious bounds and hydrodynamics do not follow from this good-scale conclusion alone.</p>


## Verification of the sharp window input {#section-window-input-verified}

<p>The <a href="/tag/MRZO/">hierarchical comparison</a> now proves the sharp critical spatial-window bound required by KPBJ for the positive radial kernel in DR1W. Its <a href="/articles/hierarchical-comparison/#section-radial-input">radial application</a> checks the norm and all small displacements explicitly. Thus the window estimate is supplied in the model assembly X8F6. The cited finite Gladkov theorem remains a separate input, and no all-scale or hydrodynamic conclusion is inferred here.</p>

## The finite three-point input is supplied {#section-good-scale-inputs-complete}

<p>The finite Gladkov theorem used in the mixed-window estimate is now proved in <a href="/tag/C7UK/">C7UK</a>, with its countable extension in <a href="/tag/87RB/">87RB</a>. Together with <a href="/tag/MRZO/">the sharp critical window estimate</a>, this supplies the two probability inputs left cited in <a href="/tag/X8F6/">the radial good-scale assembly</a>. Under its stated radial hypotheses and $d\geq3\alpha$, the good-scale conclusion now has a prose proof through the linked arguments. No all-scale fictitious estimate or hydrodynamic limit is inferred from this completion.</p>

## Modified quantiles and failure of hydrodynamics {#section-modified-quantiles}

<p>In the following sections retain the radial hypotheses and normalization of <a href="/tag/C0OR/">C0OR</a>. To keep the observation window distinct from the proper neighbours used in the derivative formula, write</p>
<div class="math-display">$$\Lambda_r=\{z\in\mathbb Z^d:\|z\|\leq r\},\qquad N_r=\Lambda_r\setminus\{0\}.$$</div>

<a id="tag-CXTO" data-assertion="definition" data-title="The modified largest-cluster quantile and hydrodynamic condition"></a>
<p>Under the law with intensity kernel $\beta_\lambda(r)J_r$, where $\beta_\lambda(r)=\beta_c(1-\lambda r^{-\alpha})$, put</p>
<div class="math-display">$$\widetilde M_\lambda(r)=\min\left\{m\geq1:
\widetilde{\mathbb P}_{r,\lambda}\left(\max_x|K_x\cap\Lambda_r|\geq m\right)\leq e^{-1}\right\}.$$</div>
<p>The modified hydrodynamic condition is the assertion that $\widetilde M_\lambda(r)=o(r^{(d+\alpha)/2})$ for every $0&lt;\lambda\leq1$. The ordinary condition is the corresponding assertion at $\lambda=0$. The quantile is nondecreasing in $r$ and nonincreasing in $\lambda$, by the monotone coupling of the kernels and windows. Thus the modified condition is equivalent to its validity for a set of positive $\lambda$ with zero as a limit point.</p>
<p>If it fails, there are $\lambda_*&gt;0$ and $c_*&gt;0$ such that $\widetilde M_\lambda(r)\geq c_*r^{(d+\alpha)/2}$ on an unbounded set of radii for every $0\leq\lambda\leq\lambda_*$. Indeed, failure gives a positive limsup at one positive parameter; decrease that parameter and use monotonicity. This is a counterfactual hypothesis in the argument below, not an asserted property of the model.</p>

## A mixed moment controlled by the window quantile {#section-mixed-window-quantile}

<a id="tag-7QDN" data-assertion="proposition" data-title="The window quantile controls the mixed second cluster moment"></a>
<p>Uniformly for $r\geq1$ and $0\leq\lambda\leq1$, write $X=|K_o|$, $W=|K_o\cap\Lambda_r|$, and $\chi=\widetilde\chi_\lambda(r)$. There is a constant $C$ depending only on the kernel and norm such that</p>
<div class="math-display">$$\widetilde{\mathbb E}_{r,\lambda}[X^2W]
\leq C\chi^{7/2}r^{\alpha/2}\widetilde M_\lambda(r)^{1/2}.$$</div>
<p><em>Proof.</em> The <a href="/tag/Y84V/">tree-graph estimate</a> gives $\mathbb E X^4\leq15\chi^7$. The rooted intersection tail in <a href="/tag/12NL/">12NL</a>, followed by <a href="/tag/BZDZ/">exponential damping</a> with $p=q=1$, gives $\mathbb E W^2\leq C\widetilde M_\lambda(r)\mathbb E W$. Domination by the full critical law and <a href="/tag/MRZO/">the sharp window bound</a> give $\mathbb E W\leq Cr^\alpha$. Cauchy–Schwarz applied to $X^2$ and $W$ now proves the estimate. Finiteness of all the full-cluster moments used here follows from DR1W. This supplies (III.3.14).</p>

## Comparing intensity derivatives at two cutoffs {#section-cutoff-derivative-transport}

<a id="tag-1AQ4" data-assertion="proposition" data-title="The normalized intensity derivative transports from large cutoffs to small ones"></a>
<p>Define the intensity derivative at a fixed cutoff by</p>
<div class="math-display">$$\widetilde D_\lambda(r)=\left.\partial_\beta\chi(\beta,r)\right|_{\beta=\beta_\lambda(r)}.$$</div>
<p>At a zero intensity use the right derivative. There is $C&lt;\infty$, independent of $\lambda,r,s$, such that</p>
<div class="math-display">$$\widetilde D_\lambda(r)\leq C\widetilde\chi_\lambda(r)^2
\left[s^{-\alpha}+s^{-2\alpha}\widetilde D_\lambda(s)\right]
\qquad(r\geq s\geq1,\ 0\leq\lambda\leq1).$$</div>
<p><em>Proof.</em> The two-cluster derivative formula gives</p>
<div class="math-display">$$\widetilde D_\lambda(r)=\sum_{y\ne0}J_r(0,y)\rho_r(0,y),\qquad
\rho_r(0,y)=\widetilde{\mathbb E}_{r,\lambda}[|K_o||K_y|\mathbf1_{\{o\nleftrightarrow y\}}].$$</div>
<p>The finite cutoff has finite susceptibility and a right neighbourhood of finite susceptibility. The integrated pivotal formula and its continuous rate therefore give the derivative at every positive intensity in question, and its right-hand value at zero. No assertion about differentiability of the quantile is involved.</p>
<p>Since $J_r-J_s\leq\min\{J,j(s)\}$, summing inside and outside the norm ball gives</p>
<div class="math-display">$$\sum_{y\ne0}(J_r-J_s)(0,y)\leq C s^{-\alpha}.$$</div>
<p>For large $s$, the inside sum is at most $|N_s|j(s)=O(s^{-\alpha})$, and the outside sum is $O(s^{-\alpha})$ by summing the power-law tail over dyadic annuli. Increasing $C$ covers $1\leq s$ in a bounded interval. The increment between the two modified intensity kernels has row sum</p>
<div class="math-display">$$\Delta_{r,s}\leq\beta_c\sum_y(J_r-J_s)(0,y)
+\beta_c\lambda(s^{-\alpha}-r^{-\alpha})\sum_yJ(0,y)
\leq C s^{-\alpha}.$$</div>
<p>Apply <a href="/tag/5FCO/">two-cluster transport</a>, using transitivity of the larger law:</p>
<div class="math-display">$$\rho_r(0,y)\leq(1+\Delta_{r,s}\widetilde\chi_\lambda(r))^2\rho_s(0,y).$$</div>
<p>The lower bound in C0OR, enlarged over bounded radii using $\chi\geq1$, gives $\widetilde\chi_\lambda(r)\geq c r^\alpha$ for all $r\geq1$, uniformly in $\lambda$. Thus $1+\Delta_{r,s}\widetilde\chi_\lambda(r)\leq C s^{-\alpha}\widetilde\chi_\lambda(r)$. Finally split $J_r=(J_r-J_s)+J_s$. For the first part, BK on the two distinct root clusters gives $\rho_r(0,y)\leq\widetilde\chi_\lambda(r)^2$. For the second part use transport and the derivative identity at $s$. The two sums give precisely the asserted bound.</p>

## Finding a large quantile at a low-susceptibility scale {#section-synchronized-scales}

<a id="tag-0HMO" data-assertion="theorem" data-title="Failure of modified hydrodynamics forces simultaneous quantile and susceptibility scales"></a>
<p>Suppose $d=3\alpha$ and the modified hydrodynamic condition fails. There are $c&gt;0$ and $0&lt;\lambda_0\leq1$ such that, whenever $0\leq\lambda\leq\lambda_0$ and</p>
<div class="math-display">$$A_\lambda=\liminf_{r\to\infty}\frac{\beta_c}{\alpha}r^{-\alpha}\widetilde\chi_\lambda(r)&lt;\infty,$$</div>
<p>there is an unbounded set of radii on which</p>
<div class="math-display">$$\widetilde\chi_\lambda(r)\leq\frac{4\alpha A_\lambda}{\beta_c}r^\alpha,
\qquad \widetilde M_\lambda(r)\geq c A_\lambda^{-3}r^{2\alpha}.$$</div>
<p><em>Proof.</em> Choose $\lambda_0$ sufficiently small that C0OR gives $A_\lambda\geq3/4$ for all $\lambda\leq\lambda_0$, and that the failure hypothesis supplies a common positive lower limsup for $r^{-2\alpha}\widetilde M_\lambda(r)$. Fix such a $\lambda$ with finite $A=A_\lambda$, and set $a=cA^{-3}$, where $c$ will be chosen independently of $A,\lambda$.</p>
<p>The derivative of the modified kernel has two nonnegative contributions. Keeping only the cutoff contribution in the exact two-cluster formula, and applying Harris before subtracting the same-cluster terms, yields almost everywhere</p>
<div class="math-display">$$\widetilde\chi_\lambda'(r)\geq\beta_\lambda(r)|j'(r)|
\left[|N_r|\widetilde\chi_\lambda(r)^2-
\widetilde{\mathbb E}_{r,\lambda}(|K_o|^2|K_o\cap N_r|)\right].$$</div>
<p>All terms are locally integrable by the compact-interval moment domination used in C0OR. By <a href="/tag/7QDN/">the mixed moment bound</a>, if $\widetilde M_\lambda(r)&lt;a r^{2\alpha}$ and $\widetilde\chi_\lambda(r)\leq(4\alpha A/\beta_c)r^\alpha$, the error divided by $|N_r|\widetilde\chi_\lambda(r)^2$ is at most $C A^{3/2}\sqrt a=C\sqrt c$ at sufficiently large radii. Choose $c$ so that this is at most $1/2$. Also choose it so that $a$ is below the common positive limsup; this is possible uniformly because $A\geq3/4$.</p>
<p>Put $q(r)=(\beta_c/\alpha)r^{-\alpha}\widetilde\chi_\lambda(r)$. It is locally absolutely continuous. On an interval where $3A\leq q(r)\leq4A$ and $\widetilde M_\lambda(r)&lt;a r^{2\alpha}$, the last derivative bound and $\beta_\lambda(r)|j'(r)||N_r|\sim\beta_c r^{-\alpha-1}$ give</p>
<div class="math-display">$$\frac{\widetilde\chi_\lambda'(r)}{\widetilde\chi_\lambda(r)}
\geq(1-o(1))\frac{3A\alpha}{2r}&gt;\frac\alpha r.$$</div>
<p>The last inequality holds at all sufficiently large radii since $3A/2\geq9/8$. Consequently $q$ is strictly increasing on such an interval.</p>
<p>Suppose the desired simultaneous scales were bounded. At every sufficiently large radius with $\widetilde M_\lambda(r)\geq a r^{2\alpha}$ we would then have $q(r)&gt;4A$. Such radii are unbounded. Choose one, and then a larger radius with $q\leq2A$, which exists because $\liminf q=A$. By continuity, between them there is a last crossing of $4A$ before the first subsequent crossing of $3A$. On the intervening interval, $3A\leq q\leq4A$; the absence of simultaneous scales forces $\widetilde M_\lambda(r)&lt;a r^{2\alpha}$ throughout. Strict increase contradicts the drop from $4A$ to $3A$. This proves the theorem.</p>
<p>This proof of Lemma III.3.14 uses neither a last attained quantile scale nor continuity of the integer-valued quantile. The source's last-scale definition and its use of a liminf where the hypothesis gives a limsup are recorded <a href="/errata/hutchcroft-lrp-3/#last-large-quantile-scale">provisionally</a>.</p>

## A derivative lower bound at every large scale {#section-fictitious-derivative}

<a id="tag-SQGG" data-assertion="theorem" data-title="The counterfactual quantile hypothesis gives an all-scale intensity derivative lower bound"></a>
<p>Under the hypotheses of 0HMO, there are constants $c,C&gt;0$ such that, for every $0\leq\lambda\leq\lambda_0$ with $A_\lambda&lt;\infty$,</p>
<div class="math-display">$$\widetilde D_\lambda(r)\geq c A_\lambda^{-12}r^{2\alpha}-Cr^\alpha
\qquad(r\geq1).$$</div>
<p>In particular,</p>
<div class="math-display">$$\liminf_{r\to\infty}r^{-2\alpha}\widetilde D_\lambda(r)\geq c A_\lambda^{-12}.$$</div>
<p>For $0&lt;\lambda\leq\lambda_0$, the good-scale susceptibility theorem gives $A_\lambda\leq C'/\lambda$, so the lower limit is at least $c'\lambda^{12}$. At $\lambda=0$ with $A_0=\infty$, the lower-limit assertion is read as the trivial bound zero.</p>
<p><em>Proof.</em> On the unbounded set supplied by 0HMO, the <a href="/tag/LQ6Y/">largest-intersection lower moment bound</a> and $|\Lambda_r|\leq Cr^{3\alpha}$ give</p>
<div class="math-display">$$m_2(r):=\widetilde{\mathbb E}_{r,\lambda}|K_o|^2
\geq c r^{-3\alpha}\widetilde M_\lambda(r)^3
\geq c A_\lambda^{-9}r^{3\alpha},\qquad
\widetilde\chi_\lambda(r)\leq C A_\lambda r^\alpha.$$</div>
<p>At large radii $\beta_\lambda(r)\in[\beta_c/2,\beta_c]$. The <a href="/tag/VW2E/">ghost derivative lower bound</a>, with its linear error retained, therefore implies</p>
<div class="math-display">$$\frac{\widetilde D_\lambda(r)}{\widetilde\chi_\lambda(r)^2}
\geq c\frac{m_2(r)}{\widetilde\chi_\lambda(r)^3}
-\frac C{\widetilde\chi_\lambda(r)}
\geq c A_\lambda^{-12}-C r^{-\alpha}.$$</div>
<p>The intensity inequality holds at the chosen intensity, not merely at almost every one: the pivotal rate is continuous on the finite-susceptibility interval, as are the moments, so its a.e. form extends by continuity. For each fixed $\lambda$ with finite $A_\lambda$, the error tends to zero along the unbounded selected set.</p>
<p>Fix any $s\geq1$ and choose a selected $r\geq s$ sufficiently large to absorb that error. Rearranging <a href="/tag/1AQ4/">derivative transport</a> gives</p>
<div class="math-display">$$\widetilde D_\lambda(s)+s^\alpha
\geq c\frac{\widetilde D_\lambda(r)}{\widetilde\chi_\lambda(r)^2}s^{2\alpha}
\geq c' A_\lambda^{-12}s^{2\alpha}.$$</div>
<p>The constants do not depend on the selected radius or on $\lambda$, proving the all-scale bound. Divide by $s^{2\alpha}$ and let $s\to\infty$. Finally, <a href="/tag/X8F6/">the good-scale susceptibility bound</a> supplies $A_\lambda\leq C'/\lambda$ at every positive $\lambda$. Taking the negative twelfth power gives a factor $\lambda^{12}$, not $\lambda^{-12}$; the sign in the source's explanatory sentence after Lemma III.3.16 is listed in the <a href="/errata/hutchcroft-lrp-3/#fictitious-lambda-power">provisional errata</a>.</p>
<p>This proves Lemma III.3.16 with an explicit lower-order error before taking the limit. It does not yet give the uniform-in-$\lambda$ derivative lower bound or the all-scale susceptibility upper bound in Proposition III.3.13; those require the subsequent argument.</p>

## Bounding the gaps between good scales {#section-fictitious-polynomial}

<a id="tag-X9SE" data-assertion="theorem" data-title="The counterfactual derivative bound makes good-scale gaps logarithmic in the parameter"></a>
<p>Suppose $d=3\alpha$ and the modified hydrodynamic condition fails. There are $C,P&lt;\infty$ and $\lambda_0&gt;0$ such that</p>
<div class="math-display">$$\limsup_{r\to\infty}r^{-\alpha}\widetilde\chi_\lambda(r)\leq C\lambda^{-P}
\qquad(0&lt;\lambda\leq\lambda_0).$$</div>
<p>More precisely, choose the common doubling threshold in the proof of X57A sufficiently large. Consecutive sufficiently large good dyadic indices then differ by at most $C\log(2/\lambda)$. The initial index may depend on $\lambda$; the constants do not.</p>
<p><em>Proof.</em> Fix $\lambda$ and abbreviate $\widetilde\chi_\lambda$ to $\chi$. Use the comparison radius $R$ from X57A, with $h=2\alpha$, and the four nondecreasing functions</p>
<div class="math-display">$$f_1=\chi,\qquad f_2=R,\qquad f_3=\chi\circ R,\qquad f_4=m_3.$$</div>
<p>Take $\mathcal K$ to contain every sufficiently large index at which $f_i(4r)\leq L f_i(r)$ for all four functions and all $r\in[2^k,2^{k+2}]$. The proof of X57A allows any sufficiently large fixed $L$ and gives this set positive lower density. On its lower half-intervals, X8F6 gives $\chi(r)\leq C\lambda^{-1}r^\alpha$.</p>
<p>By SQGG, $\widetilde D_\lambda(r)\geq c\lambda^{12}r^{2\alpha}$ eventually. The <a href="/tag/UTUF/">exploration-score upper bound</a> gives $\widetilde D_\lambda(r)^2\leq C\chi(r)m_2(r)$ at large radii. Its a.e. intensity form extends to the chosen intensity by continuity of the pivotal rate and moments, as above. On a good lower half-interval, the tree bounds and Cauchy–Schwarz therefore yield</p>
<div class="math-display">$$\begin{gathered}
c\lambda^{25}r^{3\alpha}\leq m_2(r)\leq C\lambda^{-3}r^{3\alpha},\\
c\lambda^{b}r\leq R(r)\leq C\lambda^{-1/\alpha}r,qquad b=\frac{25}{4\alpha},\\
c\lambda^{51}r^{5\alpha}\leq m_3(r)\leq C\lambda^{-5}r^{5\alpha}.
\end{gathered}$$</div>
<p>For the radius bounds use $R(r)^{4\alpha}=(4/c_0^2)\chi(r)m_2(r)$, where $c_0$ is the cap coefficient from X57A, and the uniform lower bound $\chi(r)\geq c r^\alpha$. For the third moment use $m_2^2\leq\chi m_3$ and $m_3\leq3\chi^5$.</p>
<p>Let $k_1&lt;k_2$ be consecutive good indices beyond these initial thresholds, and put $r_i=2^{k_i}$ and $g=k_2-k_1$. Reverse doubling gives $R(2r)\geq(1+\eta)R(r)$ with $\eta&gt;0$ independent of $\lambda$. Hence one can choose an integer $\ell\leq C\log(2/\lambda)$ such that, if $r'_2=2^{k_2-\ell}\geq r_1$, then</p>
<div class="math-display">$$R(r'_2)\leq(1+\eta)^{-\ell}R(r_2)\leq r_2.$$</div>
<p>If $g\leq\ell+4$, the desired gap bound already holds. Otherwise each $k=k_1+1,\ldots,k_2-\ell-4$ is bad. For at least one $i$ it satisfies</p>
<div class="math-display">$$\log f_i(2^{k+4})-\log f_i(2^k)&gt;\log L.$$</div>
<p>Sum these nonnegative increments over the bad indices and all four functions. For each function they telescope in four residue classes, with total at most $4\log(f_i(r'_2)/f_i(r_1))$. Consequently</p>
<div class="math-display">$$\max_i\frac{f_i(r'_2)}{f_i(r_1)}\geq L^{(g-\ell-4)/16}.$$</div>
<p>Monotonicity and $R(r'_2)\leq r_2$ bound the left side above by</p>
<div class="math-display">$$\max\left\{\frac{\chi(r_2)}{\chi(r_1)},\frac{R(r_2)}{R(r_1)},
\frac{\chi(r_2)}{\chi(R(r_1))},\frac{m_3(r_2)}{m_3(r_1)}\right\}
\leq C\lambda^{-Q}\left(\frac{r_2}{r_1}\right)^{5\alpha+1}$$</div>
<p>for some fixed $Q$. The endpoint estimates above give the first, second and fourth ratios. For the third, use $\chi(R(r_1))\geq cR(r_1)^\alpha\geq c\lambda^{\alpha b}r_1^\alpha$. All four ratios thus have a fixed power of $\lambda^{-1}$ and a radius exponent at most $5\alpha+1$.</p>
<p>Choose $L$ so that $L^{1/16}\geq2^{5\alpha+2}$. Since $L^{(\ell+4)/16}\leq C\lambda^{-Q'}$, the lower bound forces</p>
<div class="math-display">$$\left(\frac{r_2}{r_1}\right)^{5\alpha+2}
\leq C\lambda^{-Q-Q'}\left(\frac{r_2}{r_1}\right)^{5\alpha+1}.$$</div>
<p>This proves $r_2/r_1\leq C\lambda^{-Q-Q'}$, and hence the claimed logarithmic bound on $g$. Given any sufficiently large radius, take the next good dyadic scale. Its radius is at most a fixed power of $\lambda^{-1}$ times the original radius. Monotonicity of $\chi$ and the good-scale upper bound then prove the displayed limsup estimate.</p>
<p>The factor sixteen in the counting step keeps both overlaps explicit: four dyadic residue classes and four functions. Its value affects only the fixed doubling threshold and the unspecified power of $\lambda^{-1}$.</p>

## Removing the parameter from the capped mean {#section-fictitious-critical-cap}

<a id="tag-0NU2" data-assertion="theorem" data-title="Counterfactual all-scale susceptibility control bounds the critical capped mean"></a>
<p>Under the hypotheses of X9SE, there is $C&lt;\infty$ such that</p>
<div class="math-display">$$\mathbb E_{\beta_c,r}\min\{|K_o|,r^{2\alpha}\}\leq Cr^\alpha
\qquad(r\geq1).$$</div>
<p><em>Proof.</em> Let $0&lt;c_0\leq1$ be the cap coefficient in N3OC and set $T_\lambda(r,m)=\widetilde{\mathbb E}_{r,\lambda}\min(|K_o|,m)$. For each fixed positive $\lambda\leq\lambda_0$, the capped integral and X9SE give, at all sufficiently large $r$ depending on $\lambda$,</p>
<div class="math-display">$$r^{-\alpha}T_\lambda(r,c_0r^{2\alpha})
\leq C\int_r^{2r}s^{-\alpha-1}T_\lambda(s,c_0s^{2\alpha})\,ds
\leq C\log\frac{\widetilde\chi_\lambda(2r)}{\widetilde\chi_\lambda(r)}
\leq C'\log(2/\lambda).$$</div>
<p>The first inequality uses stochastic monotonicity and the increasing cap; the last uses the polynomial upper bound and C0OR's uniform lower bound. The constant $C'$ is independent of $\lambda$ even though the initial radius is not.</p>
<p>Fix a positive $\lambda=\lambda_*$ so small that $C'\beta_c M\lambda_*\log(2/\lambda_*)\leq1/2$, where $M=\sum_{y\ne0}J(0,y)$. For each fixed radius, apply <a href="/tag/D7A5/">the countable truncated Russo inequality</a> in the intensity variable, keeping $m=c_0r^{2\alpha}$ fixed. Cutoff susceptibility is finite throughout the interval by DR1W. Thus, with $F(\beta)=\mathbb E_{\beta,r}\min(|K_o|,m)$,</p>
<div class="math-display">$$0\leq F'(\beta)\leq MF(\beta)^2,qquad
\frac1{F(\beta_c)}\geq\frac1{F(\beta_{\lambda_*}(r))}-M\beta_c\lambda_*r^{-\alpha}.
$$</div>
<p>For sufficiently large $r$, the preceding cap estimate makes the right side at least $[2C'\log(2/\lambda_*)r^\alpha]^{-1}$. Hence the critical capped mean is at most $2C'\log(2/\lambda_*)r^\alpha$. The parameter is now fixed, so this is a constant times $r^\alpha$. Since $\min(x,r^{2\alpha})\leq c_0^{-1}\min(x,c_0r^{2\alpha})$, the desired cap follows. On the remaining bounded radius interval, use $\min(|K_o|,r^{2\alpha})\leq r^{2\alpha}$ and enlarge $C$.</p>
<p>The choice of a single small parameter is essential: no uniform initial radius in X9SE is needed. This proves Lemma III.3.18 at the critical cutoff intensity, not at the full uncut critical law.</p>

## The fictitious moment orders on every large scale {#section-fictitious-moment-orders}

<a id="tag-BTM3" data-assertion="theorem" data-title="Failure of modified hydrodynamics forces the all-scale susceptibility and moment orders"></a>
<p>Suppose $d=3\alpha$ and the modified hydrodynamic condition fails. There are $c,C&gt;0$, $\lambda_0&gt;0$ and a radius $R_0&lt;\infty$, independent of $\lambda$, such that for $0&lt;\lambda\leq\lambda_0$ and $r\geq1$,</p>
<div class="math-display">$$c r^\alpha\leq\widetilde\chi_\lambda(r)\leq C\lambda^{-1}r^\alpha,qquad
c\lambda r^{3\alpha}\leq m_2(r)\leq C\lambda^{-3}r^{3\alpha}.$$</div>
<p>For $r\geq R_0$, the intensity derivative also satisfies</p>
<div class="math-display">$$c r^{2\alpha}\leq\widetilde D_\lambda(r)\leq C\lambda^{-2}r^{2\alpha}.$$</div>
<p>The upper derivative bound holds at every $r\geq1$. The positive lower derivative bound is stated only beyond $R_0$; a small soft cutoff may have no positive bonds.</p>
<p><em>Proof.</em> Fix $\lambda$ and define</p>
<div class="math-display">$$U(r)=\left(2\sqrt{\chi(r)m_2(r)}\right)^{1/(2\alpha)}.$$</div>
<p>The same size-biased Markov estimate used in X57A gives $\chi(r)\leq2\mathbb E_r\min(|K_o|,U(r)^{2\alpha})$. The function $U$ is nondecreasing and at least one.</p>
<p>If $U(2r)\geq4r$, then $U(s)\geq s$ for $s\in[2r,4r]$. Domination by the critical cutoff at radius $U(s)$ and <a href="/tag/0NU2/">the critical cap estimate</a> give</p>
<div class="math-display">$$\chi(s)\leq2\mathbb E_{\beta_c,U(s)}\min(|K_o|,U(s)^{2\alpha})
\leq C U(s)^\alpha.$$</div>
<p>Substituting $U(s)^{4\alpha}=4\chi(s)m_2(s)$ yields $m_2(s)\geq c\chi(s)^3$ throughout that interval. The intensity part of the modified derivative therefore gives $\chi'(s)\geq\lambda s^{-\alpha-1}(a\chi(s)^2-b\chi(s))$. The threshold and reciprocal argument in 1BO9, on $[2r,4r]$, gives $\chi(2r)\leq C\lambda^{-1}r^\alpha$, and hence the same bound for $\chi(r)$.</p>
<p>Otherwise $U(2r)&lt;4r$. For $s\in[r,2r]$ we then have $U(s)\leq4s$, so $\chi(s)m_2(s)\leq Cs^{4\alpha}$. The mixed tree bound gives $m_3(s)\leq C s^{4\alpha}\chi(s)$. The cutoff part of the derivative yields $\chi'(s)\geq s^{-\alpha-1}(a\chi(s)^2-bs^\alpha\chi(s))$. The same threshold and reciprocal calculation, now on $[r,2r]$, gives the stronger bound $\chi(r)\leq Cr^\alpha$. Both derivative inequalities have uniform constants at sufficiently large radii by the model inputs to X8F6. These two cases prove the susceptibility upper bound there. On a bounded radius interval, domination by one fixed critical cutoff extends it uniformly to $r\geq1$. C0OR supplies the lower bound.</p>
<p>We next obtain a normalized intensity derivative bounded below on an unbounded set of radii, with a constant independent of $\lambda$. If the first case occurs at arbitrarily large $r$, its cubic second-moment bound and VW2E give $\widetilde D_\lambda(2r)/\chi(2r)^2\geq c$ once the linear error is absorbed. If the first case is eventually absent, the second case gives $\chi(r)\leq Cr^\alpha$ at all sufficiently large radii. Failure of the modified hydrodynamic condition supplies an unbounded set with $\widetilde M_\lambda(r)\geq c_*r^{2\alpha}$, uniformly for small $\lambda$. LQ6Y then gives $m_2(r)\geq cr^{3\alpha}\geq c'\chi(r)^3$ on those radii, and VW2E again gives the same normalized derivative lower bound.</p>
<p>In either case, transport from arbitrarily large selected radii by 1AQ4 gives</p>
<div class="math-display">$$\widetilde D_\lambda(s)\geq c s^{2\alpha}-Cs^\alpha\qquad(s\geq1).$$</div>
<p>The constants are independent of $\lambda$, although the selected radii need not be. Thus $\widetilde D_\lambda(s)\geq c's^{2\alpha}$ beyond a common radius. The exploration-score estimate $\widetilde D_\lambda(s)^2\leq C\chi(s)m_2(s)$ and the susceptibility upper bound give $m_2(s)\geq c\lambda s^{3\alpha}$ there. Since $m_2\geq1$, enlarging constants extends this lower bound over the remaining bounded radii. Finally $m_2\leq\chi^3$ and $\widetilde D_\lambda\leq M\chi^2$ give the two upper bounds.</p>
<p>This supplies the all-scale susceptibility and moment conclusions of Proposition III.3.13, keeping the small-radius derivative limitation explicit. The cap substitution uses $U(s)^\alpha$, not the $U(s)^{2\alpha}$ printed in one source display; that correction is <a href="/errata/hutchcroft-lrp-3/#cap-radius-power">provisional</a>. The counterfactual hypothesis has not been discharged: its contradiction still requires the mesoscopic and hydrodynamic arguments that follow.</p>

## Many vertices in large clusters {#section-fictitious-large-cluster-vertices}

<a id="tag-69N5" data-assertion="proposition" data-title="Counterfactual mean-field tails make large-cluster vertices abundant in a window"></a>
<p>Retain the normalized radial model of C0OR, let $d=3\alpha$, and suppose that modified hydrodynamics fails. Write $\Lambda_s=\{z:\|z\|\leq s\}$. For every $\varepsilon&gt;0$ and $\gamma&gt;0$ there exist $\delta&gt;0$ and $R&lt;\infty$ such that</p>
<div class="math-display">$$\mathbb P_{\beta_c,s}\left(
\sum_{y\in\Lambda_s}\mathbf1_{\{|K_y|\geq\delta s^{2\alpha}\}}
\geq\gamma s^{2\alpha}\right)\geq1-\varepsilon
\qquad(s\geq R).$$</div>
<p>The same estimate holds for translated windows and, by monotonicity, if the cutoff is enlarged from $s$. The initial radius may depend on $\varepsilon,\gamma$.</p>
<p><em>Proof.</em> For a fixed threshold $m\geq1$, let $I_y=\mathbf1_{\{|K_y|\geq m\}}$ and $Y=\sum_{y\in\Lambda_s}I_y$. Conditioning on a finite cluster at $y$, the exterior retains its product law. The cluster of $z$ in that exterior is stochastically dominated by the unrestricted cluster of $z$. Hence</p>
<div class="math-display">$$\mathbb P(I_y=I_z=1,\ y\nleftrightarrow z)
\leq\mathbb P(I_y=1)\mathbb P(I_z=1),
\qquad\operatorname{Cov}(I_y,I_z)\leq\mathbb P(y\leftrightarrow z).$$</div>
<p>Cutoff clusters are finite by DR1W, so this conditioning exhausts the law. The <a href="/tag/MRZO/">sharp critical window bound</a> and domination by the full critical law give</p>
<div class="math-display">$$\operatorname{Var}(Y)\leq\sum_{y,z\in\Lambda_s}\mathbb P_{\beta_c,s}(y\leftrightarrow z)
\leq|\Lambda_s|\mathbb E_{\beta_c}|K_0\cap\Lambda_{2s}|
\leq C s^{d+\alpha}=C s^{4\alpha}.$$</div>
<p>By <a href="/tag/40HT/">the lower tail in its specified cutoff window</a>, if $m=\delta s^{2\alpha}\geq1$ and $\delta$ is below its fixed coefficient,</p>
<div class="math-display">$$\mathbb EY=|\Lambda_s|\mathbb P_{\beta_c,s}(|K_0|\geq m)
\geq c\delta^{-1/2}s^{2\alpha}.$$</div>
<p>First choose $\delta$ so small that this is at least $2\gamma s^{2\alpha}$. Chebyshev's inequality then bounds $\mathbb P(Y&lt;\gamma s^{2\alpha})$ by $4\operatorname{Var}(Y)/(\mathbb EY)^2\leq C'\delta$. Shrink $\delta$ again to make this at most $\varepsilon$, and choose $R$ large enough for $m\geq1$ and the lattice-volume bounds. The coefficient-one tail range left open in III.3.20 is not needed here.</p>

## Distinct large clusters supply a derivative surplus {#section-fictitious-local-pair-surplus}

<a id="tag-20LA" data-assertion="proposition" data-title="A large intersection quantile forces a locally large distinct-cluster contribution"></a>
<p>Under the same model and counterfactual failure hypothesis, let $M_0(r)$ be the critical-cutoff quantile of $\max_x|K_x\cap\Lambda_r|$. For every $\eta&gt;0$ there are $c&gt;0$ and $R&lt;\infty$ such that whenever $r\geq R$ and $M_0(r)\geq\eta r^{2\alpha}$,</p>
<div class="math-display">$$\mathbb E_{\beta_c,r}\left[
\mathbf1_{\{|K_0\cap\Lambda_{2r}|\geq c r^{2\alpha}\}}
\sum_{y\in\Lambda_r}\mathbf1_{\{0\nleftrightarrow y\}}|K_y|
\right]\geq c r^{3\alpha}.$$</div>
<p>The intensity here is $\beta_c$. The conclusion is not asserted at an arbitrary smaller intensity.</p>
<p><em>Proof.</em> Set $Z_t=\max_x|K_x\cap\Lambda_t|$ under the cutoff-$r$ law. Quantile minimality gives</p>
<div class="math-display">$$\mathbb P(Z_r\geq M_0(r)-1)&gt;e^{-1},\qquad
M_0(r)-1\geq M_0(r)/2\geq(\eta/2)r^{2\alpha}.$$</div>
<p>The full critical tail upper bound in 40HT and <a href="/tag/UVQ6/">finite-window hyperscaling</a> give a quantile at most $C_0r^{2\alpha}$ for $Z_{2r}$. The <a href="/tag/12NL/">exponential quantile tail</a> therefore allows a fixed $C$ with</p>
<div class="math-display">$$\mathbb P(Z_{2r}&gt;Cr^{2\alpha})&lt;1/(4e).$$</div>
<p>Cover $\Lambda_r$ by at most $N$ lattice-centred balls $D_i$ of radius $r/4$, with centres in $\Lambda_r$, where $N$ depends only on the norm and dimension. Such a cover follows from a maximal $r/4$-separated set and the volume packing bound, for sufficiently large $r$. Each $D_i\subseteq\Lambda_{2r}$ has diameter at most $r/2$.</p>
<p>Apply 69N5 at scale $r/4$ in each translated ball, then increase the cutoff to $r$. Choose its threshold coefficient and error so that, for one fixed $\delta&gt;0$, with probability at least $1-1/(4e)$,</p>
<div class="math-display">$$\#\{y\in D_i:|K_y|\geq\delta r^{2\alpha}\}\geq2Cr^{2\alpha}
\quad\text{for every }i.$$</div>
<p>Consequently all three events occur together with probability at least $1/(2e)$. On their intersection choose a cluster $A$ with $|A\cap\Lambda_r|\geq(\eta/2)r^{2\alpha}$. For each $x\in A\cap\Lambda_r$, take a covering ball $D_i$ containing $x$. It lies in $\Lambda_r(x)$. At most $Cr^{2\alpha}$ of its vertices belong to $A$, since $D_i\subseteq\Lambda_{2r}$ and $Z_{2r}\leq Cr^{2\alpha}$. Thus at least $Cr^{2\alpha}$ of its large-cluster vertices lie outside $K_x=A$, and</p>
<div class="math-display">$$\sum_{y\in\Lambda_r(x)}\mathbf1_{\{x\nleftrightarrow y\}}|K_y|
\geq C\delta r^{4\alpha}.$$</div>
<p>Also $A\cap\Lambda_r\subseteq K_x\cap\Lambda_{2r}(x)$. Sum the corresponding rooted observable over these at least $(\eta/2)r^{2\alpha}$ choices of $x$. Its sum over all $x\in\Lambda_r$ is at least $c_0r^{6\alpha}$ on an event of probability $1/(2e)$. Translation invariance identifies the expectation of this sum with $|\Lambda_r|$ times the expectation at the root. Since $|\Lambda_r|\leq C'r^{3\alpha}$, division proves the claim after reducing $c$ to meet both displayed bounds.</p>
<p>This supplies the locally large contribution in Lemma III.4.4 from the smaller cutoff-tail window already proved. It does not establish the supremum-over-forbidden-sets conclusion of III.4.1 or the final contradiction; those still require the averaged geodesic argument and the subsequent differential estimates.</p>


## Uniform control after deleting vertices {#section-gluing-uniform-error}

<a id="tag-JY26" data-assertion="proposition" data-title="Mesoscopic negligibility makes the restricted-cluster comparison uniform over forbidden sets"></a>
<p>Use the normalized radial model of C0OR with $d=3\alpha$, and suppose modified hydrodynamics fails. Assume also the finite nonmonotone Reimer inequality stated in <a href="/tag/X86B/">X86B</a>. Fix $\lambda\in[0,1]$, and consider an unbounded set $\mathscr R$ of radii on which $\chi_\lambda(r)\leq Cr^\alpha$. Expectations below use the law at intensity $\beta_\lambda(r)$ and cutoff $r$. Put</p>
<div class="math-display">$$\Lambda_r=\{x:\|x\|\leq r\},\qquad
\mu_r(x)=\frac{\mathbb E[|K_0|\mathbf1_{\{x\in K_0\}}]}{\mathbb E|K_0|^2},\qquad
V_r(H)=\sum_x\mu_r(x)|H\cap(x+\Lambda_r)|,$$</div>
<div class="math-display">$$S_r=\sum_{y\in\Lambda_r}\mathbf1_{\{0\nleftrightarrow y\}}|K_y|.$$</div>
<p>Let $\delta(r)&gt;0$ tend to zero along $\mathscr R$. For each such radius let $\mathscr A_r$ be a downward-closed class of finite root-containing vertex sets, every member of which satisfies $V_r(H)\leq\delta(r)r^{2\alpha}$. There is $\varepsilon(r)\to0$, independent of the class and of the deterministic forbidden set $W$, such that</p>
<div class="math-display">$$\frac{\mathbb E[S_r|K_0^W|\mathbf1_{\{K_0^W\in\mathscr A_r\}}]}{|\Lambda_r|\chi_\lambda(r)}
\geq\mathbb E[|K_0^W|;K_0^W\in\mathscr A_r]-\varepsilon(r)r^\alpha
\qquad(r\in\mathscr R\text{ sufficiently large}).$$</div>
<p>As before, $K_0^W$ is empty if $0\in W$; its contribution is then zero. Membership in $\mathscr A_r$ refers to the cluster's vertex set.</p>
<p><em>Proof.</em> Set $m=\delta(r)r^{2\alpha}$ and</p>
<div class="math-display">$$t_r=\mathbb E_{\beta_c,r}\min(|K_0|,m),\qquad
\ell_r=\sqrt{r^\alpha t_r}.$$</div>
<p>The <a href="/tag/Q7O9/">mesoscopic bound</a> gives $t_r=o(r^\alpha)$. Consequently</p>
<div class="math-display">$$\frac{\ell_r}{r^\alpha}=\frac{t_r}{\ell_r}
=\sqrt{\frac{t_r}{r^\alpha}}\longrightarrow0.$$</div>
<p>Let $P_W=\mathbb E[|K_0^W|;K_0^W\in\mathscr A_r]$. The <a href="/tag/X86B/">path truncation estimate</a> gives $\mathbb E Z_{W,\ell_r}\geq P_W-\chi_\lambda t_r/\ell_r$, since the modified law is dominated by the critical cutoff. The <a href="/tag/XFCJ/">restricted-cluster comparison</a>, with its consistent paths and hereditary class, then yields</p>
<div class="math-display">$$\frac{\mathbb E[S_r|K_0^W|\mathbf1_{\mathscr A_r}]}{|\Lambda_r|\chi_\lambda}
\geq(1-\theta_r)\left(P_W-\frac{\chi_\lambda t_r}{\ell_r}\right),\qquad
\theta_r=\frac{\ell_r m_{2,\lambda}}{|\Lambda_r|\chi_\lambda}.$$</div>
<p>Here $\theta_r\leq C'\ell_r/r^\alpha=o(1)$ by the tree-graph bound $m_{2,\lambda}\leq\chi_\lambda^3$ and $|\Lambda_r|\asymp r^{3\alpha}$. In particular its coefficient is nonnegative at all sufficiently large radii. Since $P_W\leq\chi_\lambda\leq Cr^\alpha$, the loss is at most $\theta_r\chi_\lambda+\chi_\lambda t_r/\ell_r=o(r^\alpha)$, uniformly in $W$ and the class. This proves the assertion. It is the normalized error that vanishes; the unnormalized quantity $r^\alpha t_r/\ell_r=\ell_r$ need not tend to zero.</p>

## A deficit when normalized susceptibility has a finite lower limit {#section-gluing-bounded-susceptibility}

<a id="tag-9CER" data-assertion="theorem" data-title="Conditional gluing deficit along scales with bounded normalized critical susceptibility"></a>
<p>Retain the model, failure hypothesis and finite Reimer premise of JY26. Suppose</p>
<div class="math-display">$$A:=\liminf_{r\to\infty}\frac{\beta_c\chi_0(r)}{\alpha r^\alpha}&lt;\infty.$$</div>
<p>There are deterministic probability measures $\nu_r$ on $\mathbb Z^d$, constants $\delta,\kappa&gt;0$ and $C&lt;\infty$, and an unbounded set $\mathscr R$ such that, for every $r\in\mathscr R$,</p>
<div class="math-display">$$\chi_0(r)\leq Cr^\alpha,\qquad
\sup_{W\subseteq\mathbb Z^d}\mathbb E_{\beta_c,r}\left[|K_0^W|;
\sum_x\nu_r(x)|K_0^W\cap(x+\Lambda_r)|\leq\delta r^{2\alpha}\right]
\leq(1-\kappa)\frac\alpha{\beta_c}r^\alpha.$$</div>
<p>The measures and constants do not depend on $W$. The set $W$ is deterministic, and the supremum need not be attained.</p>
<p><em>Proof.</em> C0OR gives $A\geq1$. Write $q(r)=\beta_c\chi_0(r)/(\alpha r^\alpha)$ and $\mathscr R_0=\{r\geq1:q(r)\leq2A\}$. This set is unbounded. At each sufficiently large radius choose a deterministic cover</p>
<div class="math-display">$$\Lambda_{2r}\subseteq\bigcup_{i=1}^N(c_i(r)+\Lambda_r)$$</div>
<p>with lattice centres and a fixed finite $N$. A maximal separated set and the norm-ball packing estimate give such a bound; repeat centres if necessary to obtain exactly $N$ terms. Let $\mu_r$ be the squared-volume-biased measure in JY26 and put</p>
<div class="math-display">$$\nu_r=\frac12\mu_r+\frac1{2N}\sum_{i=1}^N\delta_{c_i(r)}.$$</div>
<p>For every finite set $H$, a bound $\sum_x\nu_r(x)|H\cap(x+\Lambda_r)|\leq u r^{2\alpha}$ implies both $V_r(H)\leq2u r^{2\alpha}$ and $|H\cap\Lambda_{2r}|\leq2Nu r^{2\alpha}$. This keeps the final statement at radius $r$ while controlling the larger rooted window.</p>
<p>Suppose no strict deficit occurs along $\mathscr R_0$. Then for every fixed $u&gt;0$ the lower limit of the normalized supremum in the statement is at least $\alpha/\beta_c$. For every $v&gt;0$, the same is therefore true with the indicator of the downward-closed class</p>
<div class="math-display">$$\mathscr A_r(v)=\{H:0\in H,\ V_r(H)\leq v r^{2\alpha},\ |H\cap\Lambda_{2r}|\leq v r^{2\alpha}\},$$</div>
<p>because the averaged constraint with coefficient $u=v/(2N)$ implies membership in this class. Choose increasing radii $R_n\to\infty$ so that for $r\in\mathscr R_0$, $r\geq R_n$, the supremum for $\mathscr A_r(1/n)$ is at least $(\alpha/\beta_c-1/n)r^\alpha$. Setting $\delta(r)=1/n$ on $[R_n,R_{n+1})$ gives $\delta(r)\to0$ and</p>
<div class="math-display">$$P(r):=\sup_W\mathbb E_{\beta_c,r}[|K_0^W|;K_0^W\in\mathscr A_r(\delta(r))]
\geq\left(\frac\alpha{\beta_c}-o(1)\right)r^\alpha
\qquad(r\in\mathscr R_0).$$</div>
<p>By JY26 and $\beta_c|j'(r)||\Lambda_r|\sim\beta_c r^{-\alpha-1}$,</p>
<div class="math-display">$$\frac{r\beta_c|j'(r)|}{\chi_0(r)}
\sup_W\mathbb E_{\beta_c,r}[S_r|K_0^W|\mathbf1_{\mathscr A_r(\delta(r))}]
\geq\alpha-o(1).$$</div>
<p>These are numerical suprema at a fixed radius; no measurable choice of a maximizing forbidden set is required.</p>
<p>We show that $q(r)\to1$. Fix $1&lt;\gamma&lt;2A$ and restrict attention to the band $\gamma\leq q(r)\leq2A$. The exact cutoff identity and Harris imply, with $X=|K_0|$,</p>
<div class="math-display">$$\chi_0'(r)=\beta_c|j'(r)|\mathbb E[S_rX]
\geq\beta_c|j'(r)|\left(|\Lambda_r|\chi_0(r)^2-
\mathbb E[X^2|K_0\cap\Lambda_r|]\right)\quad\text{a.e.}$$</div>
<p>The <a href="/tag/7QDN/">mixed-moment estimate</a> shows that, if $M_0(r)\leq\eta r^{2\alpha}$, the subtracted term divided by $|\Lambda_r|\chi_0(r)^2$ is at most $C_A\sqrt\eta$. Since $\gamma&gt;1$, choosing $\eta&gt;0$ small enough gives $r\chi_0'(r)/\chi_0(r)\geq\alpha+b_1$ throughout this part of the band, for some $b_1&gt;0$ and all sufficiently large radii outside the derivative's null set.</p>
<p>On the remaining part, $M_0(r)\geq\eta r^{2\alpha}$. The <a href="/tag/20LA/">local pair surplus</a> supplies $c&gt;0$ with</p>
<div class="math-display">$$\mathbb E[S_r\mathbf1_{\{|K_0\cap\Lambda_{2r}|\geq cr^{2\alpha}\}}]\geq cr^{3\alpha}.$$</div>
<p>Once $\delta(r)\leq c/2$, every $W$ satisfies the pointwise bound</p>
<div class="math-display">$$X-|K_0^W|\mathbf1_{\mathscr A_r(\delta(r))}
\geq\frac c2r^{2\alpha}\mathbf1_{\{|K_0\cap\Lambda_{2r}|\geq cr^{2\alpha}\}}.$$</div>
<p>If the restricted cluster is in the class, its intersection with $\Lambda_{2r}$ is small; otherwise its contribution on the left is zero. Multiply by $S_r$, take expectations and the supremum over $W$, and use the preceding averaged bound. The added term before multiplication by $\beta_c|j'(r)|$ is at least $(c^2/2)r^{5\alpha}$. Since $d=3\alpha$, $|j'(r)|\sim r^{-4\alpha-1}$ and $\chi_0(r)\leq(2A\alpha/\beta_c)r^\alpha$, this gives $r\chi_0'(r)/\chi_0(r)\geq\alpha+b_2$ for some $b_2&gt;0$ at every sufficiently large radius in this part of the band, again almost everywhere.</p>
<p>Thus $(\log q)'\geq b/r$ almost everywhere whenever $\gamma\leq q\leq2A$, with $b&gt;0$. The function $q$ is locally absolutely continuous. It cannot cross this band downwards: integration between a last upper-level visit and a first lower-level visit would give a positive change of $\log q$. Nor can it remain in the band forever, since $\int dr/r$ diverges. If it exceeds $\gamma$ at a sufficiently large radius, it must eventually stay above $2A$, contrary to $\liminf q=A$. Hence $\limsup q\leq\gamma$. Letting $\gamma\downarrow1$ and using C0OR proves $q\to1$. In particular, $A=1$ and $\mathscr R_0$ contains every sufficiently large radius.</p>
<p>Failure of modified hydrodynamics gives an $\eta_0&gt;0$ and unboundedly many radii with $M_0(r)\geq\eta_0r^{2\alpha}$, by monotone domination of a failing modified law. At each such radius, quantile minimality gives probability greater than $e^{-1}$ that some cluster meets $\Lambda_r$ in at least $(\eta_0/2)r^{2\alpha}$ vertices. For every one of those vertices $x$, that intersection lies in $K_x\cap\Lambda_{2r}(x)$. Counting these roots and using translation invariance yields</p>
<div class="math-display">$$\mathbb P_{\beta_c,r}(|K_0\cap\Lambda_{2r}|\geq(\eta_0/2)r^{2\alpha})
\geq c_0r^{-\alpha}.$$</div>
<p>For $\delta(r)\leq\eta_0/4$, the same pointwise subtraction as above now gives $\chi_0(r)-P(r)\geq c_1r^\alpha$, uniformly over the forbidden set. This contradicts $\chi_0(r)/r^\alpha\to\alpha/\beta_c$ and the lower bound for $P(r)$. Therefore some averaged cap has a strict lower-limit deficit along $\mathscr R_0$. Choose a smaller positive gap and an unbounded subset on which it holds pointwise. This gives the asserted $\delta,\kappa,C,\mathscr R$.</p>

## A deficit when normalized susceptibility diverges {#section-gluing-divergent-susceptibility}

<a id="tag-F42K" data-assertion="theorem" data-title="Conditional gluing deficit for every sufficiently small positive modification parameter"></a>
<p>Retain the model, failure hypothesis and finite Reimer premise of JY26, and instead suppose $\chi_0(r)/r^\alpha\to\infty$. There is $\lambda_1&gt;0$ such that for every $0&lt;\lambda\leq\lambda_1$ there is $\delta&gt;0$ with</p>
<div class="math-display">$$\liminf_{r\to\infty}r^{-\alpha}
\sup_{W\subseteq\mathbb Z^d}\widetilde{\mathbb E}_{r,\lambda}\left[|K_0^W|;
V_{r,\lambda}(K_0^W)\leq\delta r^{2\alpha}\right]
&lt; a_\lambda:=\frac{\alpha}{\beta_c(1+\alpha\lambda M)}.$$</div>
<p>Here $M=\sum_{z\ne0}J(0,z)$, and $V_{r,\lambda}$ uses exactly the squared-volume-biased measure $\mu_{r,\lambda}$ in JY26. The cap coefficient may depend on $\lambda$. No additional bound on $|K_0^W\cap\Lambda_r|$ is imposed.</p>
<p><em>Proof.</em> The <a href="/tag/AGX4/">reciprocal comparison</a> and <a href="/tag/BTM3/">all-scale upper bound</a> give, for every fixed sufficiently small positive $\lambda$ and all sufficiently large $r$,</p>
<div class="math-display">$$\frac{r^\alpha}{2\lambda\beta_cM}\leq\chi_\lambda(r)\leq C\lambda^{-1}r^\alpha.$$</div>
<p>The constants below are uniform for these small parameters, although an initial radius may depend on the chosen parameter. By <a href="/tag/XHJ4/">the uniform cubic-moment lower bound</a> and <a href="/tag/VW2E/">the ghost derivative estimate</a>, the fixed-cutoff intensity derivative satisfies</p>
<div class="math-display">$$\frac{D_\lambda(r)}{\chi_\lambda(r)}\geq k\chi_\lambda(r)-C_0$$</div>
<p>with $k&gt;0$, once $\beta_\lambda(r)\in[\beta_c/2,\beta_c]$. The estimate holds at the actual intensity used by the path: the pivotal rate and moments are continuous on a finite-susceptibility intensity neighbourhood, so the almost-everywhere intensity inequality extends there by continuity. Such a neighbourhood exists for each finite cutoff by DR1W and right-openness.</p>
<p>The integrated Russo identity for the whole increasing kernel $\beta_\lambda(r)J_r$ gives, almost everywhere in $r$,</p>
<div class="math-display">$$\chi_\lambda'(r)=\beta_\lambda(r)|j'(r)|\widetilde{\mathbb E}_{r,\lambda}[S_r|K_0|]
+\alpha\lambda\beta_c r^{-\alpha-1}D_\lambda(r).$$</div>
<p>It follows from the preceding lower bound on $\chi_\lambda$ that the second term, divided by $\chi_\lambda$, is at least $b/r$ for some $b&gt;0$ independent of sufficiently small $\lambda$, at all sufficiently large radii. Indeed its positive part is at least $\alpha k/(2Mr)$, whereas the linear error contributes only $O(\lambda r^{-\alpha-1})$. This uses the uniform cubic moment bound at every scale, so no selection of good dyadic intervals is needed.</p>
<p>Fix such a parameter and suppose the asserted deficit fails for every $\delta&gt;0$. The diagonal choice used in 9CER gives $\delta(r)\to0$ for which the supremum over the class $\mathscr A_r=\{H:0\in H,\ V_{r,\lambda}(H)\leq\delta(r)r^{2\alpha}\}$ is at least $(a_\lambda-o(1))r^\alpha$. This class is downward closed. Apply JY26, using the fixed-parameter bound $\chi_\lambda\leq C\lambda^{-1}r^\alpha$, and then take the supremum over $W$. Since $|K_0^W|\mathbf1_{\mathscr A_r}\leq|K_0|$ and $r^\alpha\beta_\lambda(r)|j'(r)||\Lambda_r|\sim\beta_c/r$, the cutoff part gives</p>
<div class="math-display">$$\frac{\beta_\lambda(r)|j'(r)|}{\chi_\lambda(r)}
\widetilde{\mathbb E}_{r,\lambda}[S_r|K_0|]
\geq\frac{\beta_c a_\lambda-o(1)}r.$$</div>
<p>Combining the two contributions yields</p>
<div class="math-display">$$(\log\chi_\lambda)'(r)\geq
\frac{\alpha/(1+\alpha\lambda M)+b-o(1)}r.$$</div>
<p>Choose $\lambda_1$ small enough that $\alpha/(1+\alpha\lambda M)\geq\alpha-b/4$ for $0&lt;\lambda\leq\lambda_1$. For each fixed such parameter, the error is eventually at most $b/4$. Integration would then force $\chi_\lambda(r)\geq c_\lambda r^{\alpha+b/2}$, contradicting $\chi_\lambda(r)\leq C\lambda^{-1}r^\alpha$. Thus the deficit holds for every parameter in the stated interval.</p>
<p>Together, 9CER and F42K supply the two alternatives of Lemma III.4.1, conditional on finite nonmonotone Reimer. In either alternative one may select an increasing sequence of admissible radii with consecutive ratio at least 32, retain a fixed strict gap, and decrease the cap coefficient so that the gap is at least $1-(1-\delta)^3$. In the positive-parameter case the susceptibility bound on this sequence follows from BTM3. The subsequent estimate for many good scales and the final hydrodynamic contradiction are separate arguments.</p>
<p>The <a href="/errata/hutchcroft-lrp-3/#gluing-window-radius">window correction</a>, <a href="/errata/hutchcroft-lrp-3/#gluing-normalized-errors">normalization corrections</a> and <a href="/errata/hutchcroft-lrp-3/#gluing-modified-growth">modified-law correction</a> are provisional pending source-author confirmation. The proof retains the finite Reimer premise and does not assert a new formalized theorem.</p>


## The rate of the missing edge layer {#section-missing-intensity-coefficient}

<a id="tag-NE2Q" data-assertion="proposition" data-title="The missing intensity row has the coefficient used in the gluing threshold"></a>
<p>In the normalized radial model of C0OR, put $k_{s,\lambda}(z)=\beta_\lambda(s)J_s(0,z)$ and $M=\sum_{z\ne0}J(0,z)$. For every fixed $0\leq\lambda\leq1$,</p>
<div class="math-display">$$\rho_\lambda(s):=\sum_{z\ne0}\bigl(\beta_cJ(0,z)-k_{s,\lambda}(z)\bigr)
\sim\frac{\beta_c(1+\alpha\lambda M)}\alpha s^{-\alpha}
\qquad(s\to\infty).$$</div>
<p><em>Proof.</em> Since $j$ decreases to zero,</p>
<div class="math-display">$$J(0,z)-J_s(0,z)=\min\{j(\|z\|),j(s)\}
=\int_{\max\{s,\|z\|\}}^\infty |j'(u)|\,du.$$</div>
<p>Tonelli and the normalized lattice-point asymptotic give</p>
<div class="math-display">$$\sum_{z\ne0}(J-J_s)(0,z)
=\int_s^\infty |j'(u)|\,|\Lambda_u\setminus\{0\}|\,du
\sim\int_s^\infty u^{-\alpha-1}\,du=\frac{s^{-\alpha}}\alpha.$$</div>
<p>Also $\sum_zJ_s(0,z)\to M$ by monotone convergence. The identity</p>
<div class="math-display">$$\rho_\lambda(s)=\beta_c\sum_{z\ne0}(J-J_s)(0,z)
+\beta_c\lambda s^{-\alpha}\sum_{z\ne0}J_s(0,z)$$</div>
<p>now proves the claim. In particular $\rho_\lambda(s)$ is finite and bounds the row of every later increment $k_{t,\lambda}-k_{s,\lambda}$. This proves the coefficient in (III.4.1); it is a row of intensities, not of bond probabilities.</p>

## Few small-volume scales under cluster-size weighting {#section-many-scales-single-cluster}

<a id="tag-2YIE" data-assertion="theorem" data-title="A strict gluing deficit gives exponential decay for many small-volume scales uniformly over deleted domains"></a>
<p>Assume the normalized radial model with $d=3\alpha$, failure of modified hydrodynamics, and finite nonmonotone Reimer as in JY26. Choose $\lambda=0$ in the finite-lower-limit alternative of 9CER, or fix an allowed sufficiently small positive $\lambda$ in the divergent alternative of F42K. Write $\chi(s)=\chi_\lambda(s)$ and use the increasing exponential-clock coupling of $k_{s,\lambda}$. There are deterministic probability measures $\nu_s$, a sequence $r_1&lt;r_2&lt;\cdots$ with $r_{j+1}\geq32r_j$, and constants $d_0,\varepsilon&gt;0$, $C&lt;\infty$, $q,\vartheta\in(0,1)$ such that the following holds.</p>
<p>For a deterministic deleted set $W$ and a root $y$, call a selected scale $s$ small for this cluster if</p>
<div class="math-display">$$\sum_x\nu_s(x)|K_y^{s,W}\cap(x+\Lambda_{4s})|&lt;d_0s^{2\alpha}.$$</div>
<p>For every nonempty finite set $I$ of selected scales, every $R\geq\max I$, and every $\|y\|\leq\min I$,</p>
<div class="math-display">$$\mathbb E\left[|K_y^{R,W}|;\ \text{every scale in }I\text{ is small}\right]
\leq Cq^{|I|}\chi(R),$$</div>
<div class="math-display">$$\mathbb E\left[|K_y^{R,W}|;\ \#\{s\in I:s\text{ is small}\}\geq(1-\varepsilon)|I|\right]
\leq C\vartheta^{|I|}\chi(R).$$</div>
<p>All constants and the sequence are independent of $W,y,I,R$. They may depend on the fixed parameter $\lambda$. Also $\sup_j r_j^{-\alpha}\chi(r_j)&lt;\infty$.</p>
<p><em>Proof.</em> The two <a href="/tag/9CER/">gluing</a> <a href="/tag/F42K/">alternatives</a> give an unbounded set $\mathscr R'$ and, after decreasing a cap coefficient $0&lt;d_0\leq1/4$, constants</p>
<div class="math-display">$$q=1-d_0,\qquad a=\frac\alpha{\beta_c(1+\alpha\lambda M)},\qquad C_0&lt;\infty$$</div>
<p>such that, for every $s\in\mathscr R'$ beyond a fixed radius,</p>
<div class="math-display">$$\chi(s)\leq C_0s^\alpha,\qquad
\sup_D\mathbb E\left[|K_0^{s,D}|;
\sum_x\nu_s(x)|K_0^{s,D}\cap(x+\Lambda_s)|\leq d_0s^{2\alpha}\right]
\leq q^3a s^\alpha.$$</div>
<p>Here $\nu_s$ is the mixed measure in the first alternative and the squared-volume-biased measure in the second. By NE2Q we may also assume $\rho(s):=\rho_\lambda(s)\leq q^{-1}a^{-1}s^{-\alpha}$. Put</p>
<div class="math-display">$$T(s,L)=\sum_{\|z\|&gt;L}\bigl(\beta_cJ(0,z)-k_{s,\lambda}(z)\bigr),\qquad
U(s,L)=\mathbb E|K_0^s\setminus\Lambda_L|.$$</div>
<p>For each fixed $s$, both quantities tend to zero as $L\to\infty$: the intensity row is summable and the cutoff susceptibility is finite. Choose $r_1\in\mathscr R'$ large enough for all preceding bounds. Having chosen $r_j$, choose any $r_{j+1}\in\mathscr R'$ sufficiently large that</p>
<div class="math-display">$$\left(\frac{r_j}{r_{j+1}}\right)^\alpha\leq d_0q,\qquad
r_{j+1}\geq32r_j,$$</div>
<div class="math-display">$$C_0^2r_j^\alpha T(r_j,r_{j+1}/2)\leq\frac{4^{-j}}2,\qquad
C_0\rho(r_j)U(r_j,r_{j+1}/2)\leq\frac{4^{-j}}2.$$</div>
<p>No closedness of $\mathscr R'$ or least admissible radius is needed. The first condition is the separation required for contraction; the factor $r_j^\alpha$ in the tail condition accounts for the old cluster's mean size.</p>
<p>Enumerate $I=\{s_1&lt;\cdots&lt;s_m\}$, fix $W,y$ as in the statement, and let $H_i=K_y^{s_i,W}$. Condition on the finite history $H_1,\ldots,H_i$, with $s=s_i$ and $t=s_{i+1}$. Apply <a href="/tag/WKM2/">the conditional growth estimate</a> to the indicator of a small weighted volume at $t$. If an attachment vertex $b$ lies in $\Lambda_{2t}$, translation by $-b$ gives</p>
<div class="math-display">$$b+(x+\Lambda_t)\subseteq x+\Lambda_{4t}.$$</div>
<p>Thus the exterior component's small-volume constraint implies the radius-$t$ constraint in the gluing bound, after translating its deleted domain. Its tested mean is at most $q^3at^\alpha$. For other attachment vertices, discard the test and bound the mean by $\chi(t)$. Split old vertices between $\Lambda_t$ and its complement. When an old vertex is in $\Lambda_t$ but the attachment vertex is outside $\Lambda_{2t}$, their displacement has norm greater than $t$. The resulting bound is</p>
<div class="math-display">$$\begin{aligned}
&\mathbb E[|H_{i+1}|;t\text{ small}\mid H_1,\ldots,H_i]\\
&\quad\leq |H_i|+q^2(t/s)^\alpha|H_i\cap\Lambda_t|
+\rho(s)\chi(t)|H_i\setminus\Lambda_t|
+T(s,t)\chi(t)|H_i\cap\Lambda_t|.
\end{aligned}$$</div>
<p>The preceding small-scale events are measurable with respect to this history. Multiply by their indicator, take expectations, and divide by $t^\alpha$. Define</p>
<div class="math-display">$$f_i=s_i^{-\alpha}\mathbb E[|H_i|;s_1,\ldots,s_i\text{ all small}].$$</div>
<p>If $s=r_j$ and $t=r_k$ with $k&gt;j$, then $j\geq i$, and the separation gives $(s/t)^\alpha+q^2\leq q$. For the error terms, domain deletion and translation invariance give</p>
<div class="math-display">$$\mathbb E|H_i|\leq\chi(s)\leq C_0s^\alpha,\qquad
\mathbb E|H_i\setminus\Lambda_t|\leq U(s,t/2),$$</div>
<p>because $\|y\|\leq s$ and $t\geq2s$. The chosen tail bounds apply also to skipped scales by monotonicity in their second argument. Since $\chi(t)\leq C_0t^\alpha$, we obtain</p>
<div class="math-display">$$f_{i+1}\leq qf_i+4^{-j}\leq qf_i+4^{-i},\qquad f_1\leq C_0.$$</div>
<p>Iteration yields $f_m\leq q^{m-1}(C_0+(4q-1)^{-1})$. The bound is uniform in the domain and the root.</p>
<p>It remains to pass from the last selected scale $s_m$ to the arbitrary terminal scale $R$. The unconditional-test part of WKM2 gives</p>
<div class="math-display">$$\mathbb E[|K_y^{R,W}|\mid H_1,\ldots,H_m]
\leq |H_m|(1+\rho(s_m)\chi(R)).$$</div>
<p>The same bound is immediate if $R=s_m$. C0OR gives $\chi(R)\geq cR^\alpha$, after a bounded-radius adjustment, while $\rho(s_m)\leq Cs_m^{-\alpha}$. Consequently $\chi(R)^{-1}+\rho(s_m)\leq C's_m^{-\alpha}$. Multiply by the indicator that all selected scales are small and use the bound for $f_m$. This proves the first assertion.</p>
<p>For the second, let $B$ count the small scales in a finite set $I$ of size $m$. Applying the first assertion to every subset, and increasing $C$ to cover the empty subset, gives</p>
<div class="math-display">$$\mathbb E[|K_y^{R,W}|2^B]
=\sum_{J\subseteq I}\mathbb E[|K_y^{R,W}|;J\text{ all small}]
\leq C\chi(R)(1+q)^m.$$</div>
<p>Choose $0&lt;\varepsilon&lt;1$ so that $\vartheta=(1+q)2^{\varepsilon-1}&lt;1$, and apply Markov's inequality under the measure weighted by $|K_y^{R,W}|$. This gives the desired bound without any independence assumption between the scale events.</p>

## Two clusters are locally large on many common scales {#section-many-scales-two-clusters}

<a id="tag-QXP9" data-assertion="theorem" data-title="Conditional multi-scale gluing gives exponentially few pairs with almost all scales bad"></a>
<p>Under the same hypotheses and parameter alternatives as 2YIE, there are probability measures $\nu_s$, a sequence $r_{j+1}\geq32r_j$, and constants $0&lt;\delta&lt;1$, $C&lt;\infty$ such that $\sup_j r_j^{-\alpha}\chi_\lambda(r_j)&lt;\infty$ and the following holds. Call a selected scale $s$ good for the pair $0,y$ if</p>
<div class="math-display">$$\sum_x\nu_s(x)|K_0^s\cap(x+\Lambda_{4s})|\geq\delta s^{2\alpha},\qquad
\sum_x\nu_s(x)|K_y^s\cap(x+\Lambda_{4s})|\geq\delta s^{2\alpha},$$</div>
<p>and bad otherwise. Then for all integers $n\geq0$, $N\geq1$, all $R\geq r_{n+N}$ and all $\|y\|\leq r_{n+1}$,</p>
<div class="math-display">$$\mathbb E\left[|K_0^R||K_y^R|\mathbf1_{\{0\nleftrightarrow_R y\}};
\#\{j\in\{n+1,\ldots,n+N\}:r_j\text{ is bad}\}\geq(1-\delta)N\right]
\leq C(1-\delta)^N\chi_\lambda(R)^2.$$</div>
<p>All clusters use the same increasing coupling. In the finite-lower-limit case $\lambda=0$; in the divergent case each sufficiently small positive $\lambda$ has its own constants and sequence. Finite nonmonotone Reimer remains a premise through the gluing theorem.</p>
<p><em>Proof.</em> Use the sequence and constants $d_0,\varepsilon,\vartheta$ from 2YIE. First define goodness with threshold $d_0$. Condition on the finite history of the root cluster at the $N$ selected scales and at $R$, and write $K=K_0^R$. Conditional on this history, the entire exterior edge process off $K$ retains its product law: the history depends only on edges incident to $K$, and all its boundary edges are closed through $R$. Thus if $y\notin K$, its cluster at every one of these scales equals the corresponding cluster of the independent exterior process off the now fixed set $K$.</p>
<p>Let $G$ be the set of selected scales at which the root cluster is not small, and put $g=|G|$. This set is fixed under the conditioning. If $g&lt;\varepsilon N$, 2YIE at root zero bounds the expectation of $|K|$ on this event by $C\vartheta^N\chi_\lambda(R)$. The conditional exterior mean of $|K_y^R|\mathbf1_{\{y\notin K\}}$ is at most $\chi_\lambda(R)$, so this part contributes at most $C\vartheta^N\chi_\lambda(R)^2$.</p>
<p>Now suppose $g\geq\varepsilon N$ and that at most $\varepsilon^2N$ scales are good for both clusters. At least $g-\varepsilon^2N\geq(1-\varepsilon)g$ scales in $G$ are then small for the exterior cluster at $y$. The uniform deleted-domain assertion of 2YIE applies to this fixed subset $G$: its least radius is at least $r_{n+1}\geq\|y\|$, and its greatest is at most $R$. It bounds the conditional tested mean of $|K_y^R|\mathbf1_{\{y\notin K\}}$ by $C\vartheta^g\chi_\lambda(R)\leq C\vartheta^{\varepsilon N}\chi_\lambda(R)$. Multiplication by $|K|$ and averaging therefore gives</p>
<div class="math-display">$$\mathbb E[|K_0^R||K_y^R|\mathbf1_{\{0\nleftrightarrow_R y\}};
\text{at most }\varepsilon^2N\text{ common good scales at threshold }d_0]
\leq C'\vartheta^{\varepsilon N}\chi_\lambda(R)^2.$$</div>
<p>Choose $\delta&gt;0$ no larger than $d_0$, $\varepsilon^2$ and $1-\vartheta^\varepsilon$. Decreasing the volume threshold can only add good scales. Hence the event in the statement implies at most $\varepsilon^2N$ common good scales at threshold $d_0$, while $\vartheta^{\varepsilon N}\leq(1-\delta)^N$. This proves the result.</p>
<p>This completes the conditional proof of Lemma III.4.5. The source's <a href="/errata/hutchcroft-lrp-3/#many-scales-recursion">scale-recursion corrections</a> and <a href="/errata/hutchcroft-lrp-3/#many-scales-conditioning">conditioning corrections</a> remain provisional. Replacing the averaged centres by a ball centred at the origin, and using those scales for the final hydrodynamic contradiction, are further steps.</p>


## Recentring an averaged cluster intersection {#section-quantitative-recentering}

<a id="tag-43QA" data-assertion="proposition" data-title="Cluster-partition counting quantitatively recentres any averaged intersection"></a>
<p>Let $(K_x)_{x\in\mathbb Z^d}$ be a translation-invariant random partition with finite mean cluster size $\chi=\mathbb E|K_0|$. Fix a norm, a radius $r&gt;0$, and a deterministic probability measure $\nu$ on $\mathbb Z^d$. Put</p>
<div class="math-display">$$V_b(H)=\sum_x\nu(x)|H\cap(x+\Lambda_{br})|,\qquad
\Lambda_t=\{x:\|x\|\leq t\}.$$</div>
<p>For every $m\geq0$,</p>
<div class="math-display">$$\mathbb E\left[|K_0|V_4(K_0);|K_0\cap\Lambda_{8r}|\leq m\right]
\leq m\frac{|\Lambda_{6r}|}{|\Lambda_{2r}|}\chi.$$</div>
<p>Consequently, for every $b&gt;0$,</p>
<div class="math-display">$$\mathbb E\left[|K_0|;V_4(K_0)\geq b,\ |K_0\cap\Lambda_{8r}|\leq m\right]
\leq\frac{|\Lambda_{6r}|}{|\Lambda_{2r}|}\frac m b\chi.$$</div>
<p>No independence assumption or special choice of $\nu$ is required.</p>
<p><em>Proof.</em> Sum the rooted expression over $u\in\Lambda_{2r}$, evaluating the averaged volume after translation by $-u$:</p>
<div class="math-display">$$S=\sum_{u\in\Lambda_{2r}}|K_u|V_4(K_u-u)
\mathbf1_{\{|K_u\cap(u+\Lambda_{8r})|\leq m\}}.$$</div>
<p>Consider a cluster $C$ with at least one counted root $u$. Since $\Lambda_{2r}\subseteq u+\Lambda_{8r}$, it has at most $m$ vertices in $\Lambda_{2r}$, and hence at most $m$ counted roots. For every such root, $u+(x+\Lambda_{4r})\subseteq x+\Lambda_{6r}$, so $V_4(C-u)\leq V_6(C)$. Therefore, configuration by configuration,</p>
<div class="math-display">$$S\leq m\sum_{C\text{ a cluster}}|C|V_6(C).$$</div>
<p>All clusters are finite almost surely, since the mean is finite at every vertex and the vertex set is countable. Translation invariance gives $\mathbb ES=|\Lambda_{2r}|\mathbb E[|K_0|V_4(K_0);|K_0\cap\Lambda_{8r}|\leq m]$. On the other hand, the partition identity and Tonelli give</p>
<div class="math-display">$$\mathbb E\sum_C|C|V_6(C)
=\sum_x\nu(x)\sum_{z\in x+\Lambda_{6r}}\mathbb E|K_z|
=|\Lambda_{6r}|\chi.$$</div>
<p>Divide by $|\Lambda_{2r}|$ to obtain the first bound. On $\{V_4\geq b\}$, divide its integrand by $b$ to obtain the second. In particular, with $m=\eta r^{2\alpha}$ and $b=\delta r^{2\alpha}$, the bound is $C(\eta/\delta)\chi$, uniformly in $\nu$ and $r\geq1$, because the norm-ball cardinality ratio is bounded.</p>

## Many common scales in a ball centred at the origin {#section-many-rooted-good-scales}

<a id="tag-LHT3" data-assertion="theorem" data-title="Averaged good scales yield many large rooted intersections with quantitative error"></a>
<p>Retain the radial model, counterfactual failure hypothesis, finite Reimer premise and parameter alternatives of QXP9. The sequence of selected scales can be chosen with $r_{j+1}\geq64r_j$ and $\sup_jr_j^{-\alpha}\chi_\lambda(r_j)&lt;\infty$ so that the following holds. For every $\epsilon&gt;0$ there are $\eta&gt;0$ and an integer $N_0$ such that, for every $n\geq0$, $N\geq N_0$, $R\geq r_{n+N}$ and $\|y\|\leq r_{n+1}$,</p>
<div class="math-display">$$\mathbb E\left[|K_0^R||K_y^R|\mathbf1_{\{0\nleftrightarrow_R y\}};
\#\left\{j\in\{n+1,\ldots,n+N\}:
|K_0^{r_j}\cap\Lambda_{16r_j}|,|K_y^{r_j}\cap\Lambda_{16r_j}|\geq\eta r_j^{2\alpha}\right\}\leq\eta N\right]
\leq\epsilon\chi_\lambda(R)^2.$$</div>
<p>Both intersections are with the ball centred at the origin. Constants and the sequence may depend on the fixed parameter, while $\eta,N_0$ may also depend on $\epsilon$.</p>
<p><em>Proof.</em> The recursive selection in 2YIE permits any additional fixed minimum ratio. Impose 64 in place of 32, and repeat QXP9's proof on this sequence. Write $\delta$ for its averaged-good threshold and put $\chi=\chi_\lambda$. For a selected scale $s$, denote the averaged volume using radius $4s$ by $V_s$, and let</p>
<div class="math-display">$$F_s=\{V_s(K_0^s)\geq\delta s^{2\alpha},\ |K_0^s\cap\Lambda_{8s}|\leq\eta s^{2\alpha}\}.$$</div>
<p>The <a href="/tag/43QA/">partition bound</a> gives $\mathbb E[|K_0^s|;F_s]\leq C(\eta/\delta)\chi(s)$. This event is determined by the cluster at $s$. The terminal extension in <a href="/tag/WKM2/">WKM2</a>, together with NE2Q and C0OR, implies</p>
<div class="math-display">$$\mathbb E[|K_0^R|;F_s]
\leq(1+\rho_\lambda(s)\chi(R))\mathbb E[|K_0^s|;F_s]
\leq C\chi(R)s^{-\alpha}\mathbb E[|K_0^s|;F_s]
\leq C'\frac\eta\delta\chi(R),$$</div>
<p>using $\chi(s)\leq C_0s^\alpha$ on the selected sequence. Condition next on the root-zero clusters at $s$ and $R$. On $y\notin K_0^R$, the other root lies in the unchanged product exterior of $K_0^R$, whose mean cluster size is at most $\chi(R)$. Hence, with $Z_R=|K_0^R||K_y^R|\mathbf1_{\{0\nleftrightarrow_R y\}}$,</p>
<div class="math-display">$$\mathbb E[Z_R;F_s]\leq C'\frac\eta\delta\chi(R)^2.$$</div>
<p>The same estimate holds with the roles of the roots interchanged. After translation by $-y$, the centre law becomes $\nu_s^y(x)=\nu_s(x+y)$; 43QA is uniform over all such probability measures. Since $\|y\|\leq s$, the ball $y+\Lambda_{8s}$ is contained in $\Lambda_{16s}$. Therefore a scale which is averaged-good but fails the two intersection tests in the statement contributes at most $C''(\eta/\delta)\chi(R)^2$ to the weighted expectation.</p>
<p>Take $0&lt;\eta\leq\delta/2$. If at most $\eta N$ scales pass both rooted tests, then either at most $\delta N$ scales are averaged-good, or at least $\delta N/2$ are averaged-good and fail a rooted test. QXP9 handles the first event, which has at least $(1-\delta)N$ averaged-bad scales. Markov's inequality applied to the count handles the second. Thus</p>
<div class="math-display">$$\mathbb E[Z_R;\text{at most }\eta N\text{ rooted-good scales}]
\leq\left(C(1-\delta)^N+C'\frac\eta{\delta^2}\right)\chi(R)^2.$$</div>
<p>First choose $\eta$ to make the second coefficient at most $\epsilon/2$, then choose $N_0$ for the first. This proves the result, uniformly in the starting index and the permitted root displacement. It supplies Lemma III.4.6 with an explicit quantitative recentering estimate.</p>

## The modified hydrodynamic condition {#section-modified-hydrodynamic-theorem}

<a id="tag-L3TC" data-assertion="theorem" data-title="Finite nonmonotone Reimer and the radial model imply modified critical-dimensional hydrodynamics"></a>
<p>Assume the normalized radial hypotheses of C0OR, let $d=3\alpha$, and assume finite nonmonotone Reimer as stated in X86B. Then the modified hydrodynamic condition holds:</p>
<div class="math-display">$$\widetilde M_\lambda(r)=o(r^{2\alpha})
\qquad\text{for every fixed }0&lt;\lambda\leq1.$$</div>
<p>This conclusion concerns the modified intensities $\beta_c(1-\lambda r^{-\alpha})$. The ordinary condition at $\lambda=0$ is a further transfer step.</p>
<p><em>Proof.</em> Suppose the modified condition fails. If $\liminf r^{-\alpha}\chi_0(r)&lt;\infty$, choose $\lambda=0$. Otherwise choose one positive parameter sufficiently small for the gluing and uniform cubic-moment estimates. The <a href="/tag/LHT3/">rooted-good-scale theorem</a> applies in either case. Fix a nonzero vertex $y$. We will prove</p>
<div class="math-display">$$\frac{\mathbb E[|K_0^R||K_y^R|\mathbf1_{\{0\nleftrightarrow_R y\}}]}{\chi_\lambda(R)^2}\longrightarrow0.
\tag{*}$$</div>
<p>Represent the increasing law by independent Poisson marks with cumulative edge intensity $k_{r,\lambda}(z)=\beta_\lambda(r)J_r(0,z)$ for $r\geq1$. To start from the empty graph, extend it to $r&gt;0$ using $\beta_c(1-\lambda r^{-\alpha})_+$, with value $\beta_c$ when $\lambda=0$. The cutoff kernel vanishes below the smallest positive lattice distance. The extended intensities are nondecreasing and locally absolutely continuous, and agree with the required law for $r\geq1$.</p>
<p>First work in a finite induced vertex box containing both roots. Suppress mergers between the two root components as in <a href="/tag/7IVI/">7IVI</a>, and denote the resulting components by $A_t,B_t$. If at a selected scale $s$ both $|A_s\cap\Lambda_{16s}|$ and $|B_s\cap\Lambda_{16s}|$ are at least $\eta s^{2\alpha}$, every pair of vertices in these two intersections has displacement of norm at most $32s$. Each such pair remains between the two labelled components at every later time. For large $s$,</p>
<div class="math-display">$$k_{64s,\lambda}(z)-k_{32s,\lambda}(z)
\geq\beta_\lambda(32s)\bigl(j(32s)-j(64s)\bigr)
\geq c s^{-d-\alpha}\qquad(0&lt;\|z\|\leq32s).$$</div>
<p>The first inequality uses monotonicity of the intensity and the exact soft-cutoff increment; the second uses $\beta_\lambda(32s)\geq\beta_c/2$ and the derivative asymptotic for $j$. The integrated merger rate over $[32s,64s]$ is therefore at least</p>
<div class="math-display">$$c s^{-d-\alpha}(\eta s^{2\alpha})^2=c\eta^2,$$</div>
<p>since $d=3\alpha$. The larger interval matters: pairs at distance $32s$ have zero soft-cutoff intensity at radius $32s$, so the interval $[16s,32s]$ does not give this uniform pair bound.</p>
<p>The selected scales have ratio at least 64, so these time intervals are disjoint. For a block of $N$ scales and a terminal radius at least 64 times the last one, the integrated rate is at least $c\eta^2$ times the number of rooted-good scales of the suppressed process. Applying 7IVI to the terminal product and the event that more than $\eta N$ scales are rooted-good gives</p>
<div class="math-display">$$\mathbb E\left[|K_0^R||K_y^R|\mathbf1_{\{0\nleftrightarrow_R y\}};
\text{more than }\eta N\text{ rooted-good scales}\right]
\leq e^{-c\eta^3N}\mathbb E[|A_R||B_R|]
\leq e^{-c\eta^3N}\chi_\lambda(R)^2.$$</div>
<p>The last step is the increasing-event BK consequence in 7IVI; finite-box susceptibilities are bounded by the full cutoff susceptibility. No independence assertion about adaptively selected gluing events is used.</p>
<p>This bound passes to the countable graph. For fixed $R$, the two full cutoff clusters are finite almost surely and have finite second moments by DR1W. In an increasing exhaustion by finite induced boxes, their clusters at $R$, and hence at the finitely many selected earlier scales, eventually coincide with the full clusters. The product is bounded by $|K_0^R||K_y^R|$, which is integrable by Cauchy–Schwarz. Dominated convergence therefore passes the displayed inequality to the full law. No infinite-state suppressed process is needed for this passage.</p>
<p>Now fix $\epsilon&gt;0$ and choose $\eta,N_0$ from LHT3. Choose a starting index $n$ with $r_{n+1}\geq\|y\|$, beyond the initial radius needed for the intensity bound. Let $N=N(R)$ be the largest integer with $64r_{n+N}\leq R$. Then $N(R)\to\infty$. For large $R$, LHT3 bounds the contribution with at most $\eta N$ rooted-good scales by $\epsilon\chi_\lambda(R)^2$, while the preceding inequality bounds its complement. Hence</p>
<div class="math-display">$$\frac{\mathbb E[|K_0^R||K_y^R|\mathbf1_{\{0\nleftrightarrow_R y\}}]}{\chi_\lambda(R)^2}
\leq\epsilon+e^{-c\eta^3N(R)}.$$</div>
<p>Let $R\to\infty$ and then $\epsilon\downarrow0$ to prove (*). For $y=0$ the numerator is zero.</p>
<p>By the <a href="/tag/1AQ4/">two-cluster intensity derivative formula</a>,</p>
<div class="math-display">$$\frac{\widetilde D_\lambda(R)}{\chi_\lambda(R)^2}
=\sum_{y\ne0}J_R(0,y)
\frac{\mathbb E[|K_0^R||K_y^R|\mathbf1_{\{0\nleftrightarrow_R y\}}]}{\chi_\lambda(R)^2}.$$</div>
<p>Each normalized expectation is at most one by the disjoint-tree witness argument and countable BK. Since $J_R(0,y)\leq J(0,y)$ and $\sum_yJ(0,y)&lt;\infty$, dominated convergence in this series gives $\widetilde D_\lambda(R)/\chi_\lambda(R)^2\to0$.</p>
<p>But <a href="/tag/XHJ4/">the counterfactual cubic-moment bound</a> includes $\lambda=0$ and gives $m_{2,\lambda}(R)\geq c_2\chi_\lambda(R)^3$ for the chosen parameter. The <a href="/tag/VW2E/">ghost derivative lower bound</a>, valid at the actual finite-cutoff intensity by continuity of the pivotal rate, yields for large $R$</p>
<div class="math-display">$$\frac{\widetilde D_\lambda(R)}{\chi_\lambda(R)^2}
\geq\frac{(1-e^{-1})c_2}{4\beta_c}-\frac1{\beta_c\chi_\lambda(R)}.$$</div>
<p>Here $\beta_\lambda(R)\in[\beta_c/2,\beta_c]$. C0OR gives $\chi_\lambda(R)\geq cR^\alpha$, so the right side stays bounded away from zero. This contradicts the preceding limit. The failure assumption is therefore impossible, proving the modified condition for every fixed positive parameter in its definition.</p>
<p>This completes the conditional proof of Proposition III.3.1. It uses the endpoint-inclusive cubic estimate for the critical choice $\lambda=0$, without extending a positive-parameter derivative bound to that endpoint. The finite nonmonotone Reimer theorem remains an external premise. The <a href="/errata/hutchcroft-lrp-3/#recentering-partition">partition correction</a>, <a href="/errata/hutchcroft-lrp-3/#recentering-scale-count">scale-count correction</a> and <a href="/errata/hutchcroft-lrp-3/#joining-cutoff-window">joining-window correction</a> are provisional. The ordinary hydrodynamic limit and the later three-point asymptotics are not asserted by this theorem.</p>


## Transporting local second moments {#section-local-moment-transport}

<a id="tag-9JTA" data-assertion="theorem" data-title="Local second moments obey an integral transport inequality"></a>
<p>Retain the normalized radial model of C0OR. For $r,R\geq1$ and $0\leq\beta\leq\beta_c$, write</p>
<div class="math-display">$$F_x(\beta,r;R)=\mathbb E_{\beta,r}|K_0\cap(x+\Lambda_R)|^2,
\qquad Q(\beta,r;R)=\sup_xF_x(\beta,r;R),
\qquad M=\sum_{z\ne0}J(0,z).$$</div>
<p>There is a constant $C$ depending only on the dimension and norm such that, at each fixed cutoff $r$,</p>
<div class="math-display">$$F_x(b,r;R)-F_x(a,r;R)
\leq CM\int_a^b\chi(\beta,r)Q(\beta,r;R)\,d\beta
\qquad(0\leq a\leq b\leq\beta_c).$$</div>
<p>In particular,</p>
<div class="math-display">$$Q(b,r;R)\leq Q(a,r;R)
\exp\left(CM\int_a^b\chi(\beta,r)\,d\beta\right).$$</div>
<p>The individual $F_x$ are absolutely continuous in intensity. They are also locally absolutely continuous in the cutoff radius, with</p>
<div class="math-display">$$\partial_rF_x(\beta,r;R)
\leq C\beta|j'(r)|\,|N_r|\,\chi(\beta,r)Q(\beta,r;R)
\quad\text{for almost every }r\geq1.$$</div>
<p>Thus the radius coefficient is $O(\beta r^{-\alpha-1})$ for large $r$. Neither assertion differentiates the supremum $Q$.</p>
<p><em>Proof.</em> The essential estimate concerns a nonnegative symmetric increment kernel $a(z-y)$ with row sum $h=\sum_z a(z)$. Put $W=x+\Lambda_R$. A merger from $y\in K_0$ to a distinct component $K_z$ increases the squared intersection by</p>
<div class="math-display">$$|K_z\cap W|^2+2|K_0\cap W||K_z\cap W|.$$</div>
<p>First restrict the percolation to a finite induced box containing the root. Russo's formula expresses its derivative as the sum of these increments times the edge rates. Apply increasing-event BK to the two distinct components and dominate the resulting connection probabilities by those in the full cutoff law. For the first term, the sum is at most</p>
<div class="math-display">$$\sum_{y,z}a(z-y)\tau(0,y)\mathbb E|K_z\cap W|^2
\leq h\chi Q,$$</div>
<p>where $Q=Q(\beta,r;R)$. The mixed term, before its factor two, is at most</p>
<div class="math-display">$$B=\sum_{y,z,u,v}a(z-y)
\mathbb P(0\leftrightarrow y\leftrightarrow u)\tau(z,v)
\mathbf1_{\{u,v\in W\}}.$$</div>
<p>For each summand translate by $-v$, then rename $v'=-v$, $u'=u-v$, $y'=y-v$ and $z'=z-v$. The window conditions become $v'\in-x+\Lambda_R$ and $u'-v'\in x+\Lambda_R$. In particular $u'\in\Lambda_{2R}$. Dropping only the latter difference constraint gives</p>
<div class="math-display">$$B\leq\sum_{y',z'}a(z'-y')\tau(0,z')
\mathbb E\left[|K_{y'}\cap\Lambda_{2R}|
|K_{y'}\cap(-x+\Lambda_R)|\right].$$</div>
<p>The two observation windows have different centres. Cauchy–Schwarz bounds the expectation by $\sqrt{Q(\beta,r;2R)Q}$. A norm ball of radius $2R$ can be covered by at most $L$ lattice-centred balls of radius $R$, with $L$ independent of $R$: take a maximal $R/2$-separated subset and compare the volumes of its disjoint radius-$R/4$ balls. Squaring the sum of the intersection counts gives $Q(\beta,r;2R)\leq L^2Q$. It follows that $B\leq Lh\chi Q$. The full merger bound is therefore $(1+2L)h\chi Q$.</p>
<p>For intensity variation take $a(z)=J_r(0,z)$, so $h\leq M$. Integrate the finite-box Russo formula between $a$ and $b$ and exhaust the lattice. The finite-window observables increase to $F_x$ by finite path witnesses. On a compact parameter interval the susceptibility is bounded by DR1W and $Q\leq|\Lambda_R|^2$, so the common integral bound is finite. This proves the first inequality on every subinterval and hence absolute continuity. Taking the supremum over $x$ yields</p>
<div class="math-display">$$Q(b,r;R)\leq Q(a,r;R)+CM\int_a^b\chi(\beta,r)Q(\beta,r;R)\,d\beta.$$</div>
<p>The supremum is measurable, being over countably many increasing continuous functions. Integral Gronwall proves the exponential bound. For radius variation, the increment kernel is $a(z)=\beta|j'(r)|\mathbf1_{N_r}(z)$ almost everywhere. The same integrated argument, with a fixed compact radius interval and its upper-endpoint moment bound, proves the remaining assertion.</p>
<p>This supplies the local-moment estimate needed from Lemma III.4.7 in the finite-susceptibility range used here. The corrected change of variables is recorded in the <a href="/errata/hutchcroft-lrp-3/#local-moment-translation">provisional source erratum</a>.</p>

## Susceptibility under the modified condition {#section-hydrodynamic-susceptibility}

<a id="tag-5CV7" data-assertion="theorem" data-title="Modified hydrodynamics gives the sharp critical cutoff susceptibility"></a>
<p>Assume the normalized radial hypotheses of C0OR and $d=3\alpha$. If the modified hydrodynamic condition holds, then for each fixed $0&lt;\lambda\leq1$,</p>
<div class="math-display">$$\limsup_{r\to\infty}r^{-\alpha}\chi_\lambda(r)\leq\frac\alpha{\beta_c},
\qquad\chi_0(r)\sim\frac\alpha{\beta_c}r^\alpha.$$</div>
<p><em>Proof.</em> Fix a positive $\lambda$ and abbreviate $\chi=\chi_\lambda(r)$, $X=|K_0|$ and $W=|K_0\cap\Lambda_r|$. The cutoff part of the Russo identity, followed by Harris, gives along the increasing modified path</p>
<div class="math-display">$$\chi_\lambda'(r)\geq\beta_\lambda(r)|j'(r)|
\left(|N_r|\chi^2-\mathbb E[X^2W]\right)
\quad\text{almost everywhere}.$$</div>
<p>The intensity-rate contribution is nonnegative and has been discarded. By <a href="/tag/7QDN/">the mixed quantile bound</a>,</p>
<div class="math-display">$$\frac{\mathbb E[X^2W]}{|N_r|\chi^2}
\leq C\left(\frac\chi{r^\alpha}\right)^{3/2}
\left(\frac{\widetilde M_\lambda(r)}{r^{2\alpha}}\right)^{1/2}.$$</div>
<p>The last factor tends to zero. We must first bound the susceptibility ratio before using this as a vanishing error.</p>
<p>The <a href="/tag/X8F6/">good-scale estimate</a>, whose window and finite three-point inputs were supplied above, gives an unbounded set on which $\chi/r^\alpha\leq A_\lambda$. Choose $B&gt;\max\{2A_\lambda,4\alpha/\beta_c\}$ and put $q(r)=\chi/r^\alpha$. For all sufficiently large radii at which $B/2\leq q(r)\leq B$, the preceding inequalities and $\beta_\lambda(r)|j'(r)||N_r|\sim\beta_c r^{-\alpha-1}$ give</p>
<div class="math-display">$$\frac{d}{dr}\log q(r)
\geq\frac{\beta_c q(r)/2-\alpha}{r}
\geq\frac{\beta_c B/4-\alpha}{r}&gt;0
\quad\text{almost everywhere}.$$</div>
<p>Thus $q$ cannot cross this band downwards. Indeed, integrating between its last value $B$ before its first subsequent value $B/2$ would give an increase of its logarithm. Since there are arbitrarily late values below $B/2$, no sufficiently late value can reach $B$. This proves $q(r)&lt;B$ eventually.</p>
<p>The mixed error now tends to zero along the whole tail, so</p>
<div class="math-display">$$\frac{\chi_\lambda'(r)}{\chi_\lambda(r)^2}
\geq(1-o(1))\beta_c r^{-\alpha-1}.$$</div>
<p>C0OR gives $\chi_\lambda(r)\to\infty$. Integrating the reciprocal to infinity proves the asserted upper limit for each positive $\lambda$.</p>
<p>For the critical law use <a href="/tag/AGX4/">reciprocal intensity transport</a>:</p>
<div class="math-display">$$\frac1{\chi_0(r)}\geq\frac1{\chi_\lambda(r)}-\beta_c\lambda M r^{-\alpha}.$$</div>
<p>For each fixed $\lambda&gt;0$ with $\alpha\lambda M&lt;1$, the upper limit just proved gives</p>
<div class="math-display">$$\limsup_{r\to\infty}\frac{\chi_0(r)}{r^\alpha}
\leq\frac\alpha{\beta_c(1-\alpha\lambda M)}.$$</div>
<p>Send $\lambda\downarrow0$. The matching lower limit is C0OR at $\lambda=0$. This proves the asymptotic without requiring an error estimate uniform in $\lambda$.</p>

## Ordinary critical hydrodynamics {#section-ordinary-hydrodynamic-theorem}

<a id="tag-BCKB" data-assertion="theorem" data-title="The modified condition transfers to ordinary critical hydrodynamics"></a>
<p>Under the normalized radial hypotheses of C0OR with $d=3\alpha$, the modified hydrodynamic condition implies</p>
<div class="math-display">$$\widetilde M_0(r)=o(r^{2\alpha}),\qquad
\sup_x\mathbb E_{\beta_c,r}|K_0\cap(x+\Lambda_r)|^2=o(r^{3\alpha}),
\qquad\chi_0(r)\sim\frac\alpha{\beta_c}r^\alpha.$$</div>
<p>Consequently these conclusions hold if finite nonmonotone Reimer is assumed, by L3TC. No restriction $\alpha&lt;2$ is used in this hydrodynamic transfer.</p>
<p><em>Proof.</em> The susceptibility asymptotic is <a href="/tag/5CV7/">5CV7</a>. Fix $\lambda=1/2$. Translation invariance gives the same largest-intersection quantile for every translate of $\Lambda_r$, and <a href="/tag/12NL/">rooted damping</a> permits a root outside that window. Its moment consequence BZDZ and the uniform first-moment bound <a href="/tag/MTUQ/">MTUQ</a> give</p>
<div class="math-display">$$Q(\beta_\lambda(r),r;r)
\leq C\widetilde M_\lambda(r)
\sup_x\mathbb E_{\beta_\lambda(r),r}|K_0\cap(x+\Lambda_r)|
\leq Cr^\alpha\widetilde M_\lambda(r)=o(r^{3\alpha}).$$</div>
<p>At a fixed $r$, susceptibility is increasing in intensity and is at most $\chi_0(r)\leq C'r^\alpha$ for large $r$. Apply <a href="/tag/9JTA/">the local-moment transport inequality</a> between $\beta_\lambda(r)$ and $\beta_c$. Since the interval has length $\beta_c\lambda r^{-\alpha}$,</p>
<div class="math-display">$$Q(\beta_c,r;r)
\leq Q(\beta_\lambda(r),r;r)
\exp(CC'M\beta_c\lambda)=o(r^{3\alpha}).$$</div>
<p>Finally, apply <a href="/tag/LQ6Y/">the partition moment bound</a> with exponent two and observation window $\Lambda_r$:</p>
<div class="math-display">$$\frac{\widetilde M_0(r)^3}{8e}
\leq\sum_{u\in\Lambda_r}\mathbb E_{\beta_c,r}|K_u\cap\Lambda_r|^2
\leq|\Lambda_r|Q(\beta_c,r;r)=o(r^{6\alpha}).$$</div>
<p>The second inequality translates each root and retains the resulting shifted window. Taking cube roots proves the ordinary hydrodynamic condition.</p>
<p>This completes the modified-to-critical step of Theorem III.1.11. Combining it with the preceding conditional proof of modified hydrodynamics gives a prose proof with finite nonmonotone Reimer still explicit. The quantitative rate conjecture in Remark III.1.12, the subsequent three-point asymptotics and the vertex-factor computation are separate results.</p>


## The critical second moment and its slowly varying factor {#section-critical-second-moment-variation}

<a id="tag-121D" data-assertion="theorem" data-title="Ordinary hydrodynamics makes the second-moment error vanish"></a>
<p>Assume C0OR, $d=3\alpha$, and the two conclusions</p>
<div class="math-display">$$\chi_r\sim\frac\alpha{\beta_c}r^\alpha,qquad M_r:=\widetilde M_0(r)=o(r^{2\alpha}).$$</div>
<p>Write $m_j(r)=\mathbb E_r|K_0|^j$ and $V_r=m_2(r)/\chi_r^3$. Then, with locally absolutely continuous functions and a.e. derivatives,</p>
<div class="math-display">$$\frac{\chi_r'}{\chi_r}=\frac{\alpha+o(1)}r,qquad
\frac{m_2'(r)}{m_2(r)}=\frac{3\alpha+o(1)}r,qquad
\frac{V_r'}{V_r}=\frac{o(1)}r.$$</div>
<p>The errors tend to zero uniformly on tails outside a null set. Consequently $m_2$ is regularly varying of index $3\alpha$ and $V$ is slowly varying. More precisely, for every $\eta&gt;0$ there is $R_\eta$ such that</p>
<div class="math-display">$$(s/r)^{-\eta}\leq V_s/V_r\leq(s/r)^\eta
\qquad(s\geq r\geq R_\eta).$$</div>
<p>The hypotheses are supplied by <a href="/tag/BCKB/">BCKB</a>, and therefore hold conditionally on finite nonmonotone Reimer through L3TC.</p>
<p><em>Proof.</em> Put $X=|K_0|$, $W=|K_0\cap\Lambda_r|$, $N_r=|\Lambda_r\setminus\{0\}|$ and $a(r)=\beta_c|j'(r)|N_r$. The exact hierarchy GG8B and the distinct-cluster comparison <a href="/tag/1AC7/">1AC7</a> give errors $e_1,e_2\in[0,1]$ with</p>
<div class="math-display">$$\chi_r'=a(r)\chi_r^2(1-e_1),\qquad
m_2'=3a(r)\chi_rm_2(1-e_2),$$</div>
<div class="math-display">$$e_1\leq\frac{\mathbb E_r[X^2W]}{N_r\chi_r^2},\qquad
e_2\leq\frac{\mathbb E_r[X^3W]}{N_r\chi_rm_2}.$$</div>
<p>For the lower bounds on the distinct-cluster terms, subtract their common-cluster contributions from the product bounds furnished by Harris; their sum over the rate window is bounded by the displayed numerator. All moments are finite by DR1W, so these subtractions are legitimate.</p>
<p>Rooted damping 12NL and BZDZ, followed by the critical window estimate MRZO, give $\mathbb E_rW^2\leq C r^\alpha M_r$. The <a href="/tag/65MV/">generalized tree bound</a> with $p=6,k=2$ now yields</p>
<div class="math-display">$$\mathbb E_r[X^3W]\leq\sqrt{m_6(r)\mathbb E_rW^2}
\leq C m_2(r)\chi_r^{5/2}r^{\alpha/2}\sqrt{M_r}.$$</div>
<p>Since $N_r\asymp r^{3\alpha}$ and $\chi_r\asymp r^\alpha$, it follows that $e_2\leq C\sqrt{M_r}/r^\alpha=o(1)$. The bound <a href="/tag/7QDN/">7QDN</a> at parameter zero gives the same estimate for $e_1$. These estimates hold throughout the tail, not merely along selected good scales.</p>
<p>The normalization of the cutoff rate and the susceptibility equivalent give $a(r)\chi_r\sim\alpha/r$. Substituting in the exact equations proves the first two logarithmic derivative estimates. Subtracting three copies of the first from the second also gives the exact relation</p>
<div class="math-display">$$(\log V_r)'=3a(r)\chi_r(e_1-e_2)=o(1/r).$$</div>
<p>The functions are positive and locally absolutely continuous, so their logarithms have the same regularity on compact intervals. Integrating their derivative estimates between $r$ and $cr$ proves the regular-variation assertions for every fixed $c&gt;0$. Integrating $|V'/V|\leq\eta/r$ from $r$ to any $s\geq r\geq R_\eta$ gives the final two-sided bound.</p>
<p>This supplies the critical case of Proposition I.4.15 without assuming higher-moment localization. The positive amplitude in a pure power equivalent is not asserted: the error need not be logarithmically integrable, and $V$ may tend to zero.</p>

## Critical upper bounds for every volume moment {#section-critical-volume-upper}

<a id="tag-RM79" data-assertion="theorem" data-title="The upper hierarchy propagates the critical second-moment scale"></a>
<p>Under the hypotheses of <a href="/tag/121D/">121D</a>, for every fixed integer $p\geq1$,</p>
<div class="math-display">$$\limsup_{r\to\infty}
\frac{m_p(r)}{\chi_r\bigl(m_2(r)/\chi_r\bigr)^{p-1}}
\leq(2p-3)!!,$$</div>
<p>with $(-1)!!=1$. In particular, for every integer $n\geq1$ there is a finite $D_n$ such that</p>
<div class="math-display">$$m_{2n-1}(r)\leq D_n\chi_r\bigl(m_2(r)/\chi_r\bigr)^{2n-2}\qquad(r\geq1).$$</div>
<p>If also $\alpha&lt;2$, this supplies the remaining volume hypothesis in <a href="/tag/AR3F/">AR3F</a> and <a href="/tag/3M2Y/">3M2Y</a>. Thus their mixed spatial-moment and rapid-tail conclusions hold in the critical radial model under the stated hydrodynamic/susceptibility conclusions, and conditionally on finite nonmonotone Reimer via BCKB.</p>
<p><em>Proof.</em> Put $B_p(r)=m_2(r)^{p-1}\chi_r^{2-p}$ and $d_p=(2p-3)!!$. The cases $p=1,2$ are identities. For $p\geq3$, conditioning on one finite cluster in GG8B bounds each distinct-cluster moment by the product of its marginal moments. The two endpoint terms combine by mass transport, giving</p>
<div class="math-display">$$m_p'\leq(p+1)a\chi_rm_p
+a\sum_{l=1}^{p-2}\binom pl m_{l+1}m_{p-l}\qquad\text{a.e.}$$</div>
<p>Assume the upper bounds already hold at every smaller order. Since $B_{l+1}B_{p-l}=\chi_rB_p$, their contribution to the forcing is at most</p>
<div class="math-display">$$a\chi_rB_p\left(\sum_{l=1}^{p-2}\binom pl d_{l+1}d_{p-l}+o(1)\right)
=a\chi_rB_p\bigl((p-2)d_p+o(1)\bigr).$$</div>
<p>The double-factorial identity is the one proved in <a href="/tag/5O1G/">5O1G</a>; removing the two endpoint terms from its full convolution gives the coefficient $(p-2)d_p$.</p>
<p>By 121D, $(\log B_p)'=((2p-1)\alpha+o(1))/r$ and $a\chi_r=(\alpha+o(1))/r$. Therefore $y=m_p/B_p$ satisfies</p>
<div class="math-display">$$r y'\leq-\bigl((p-2)\alpha+o(1)\bigr)y
+(p-2)\alpha d_p+o(1)\qquad\text{a.e.}$$</div>
<p>Set $g=(p-2)\alpha&gt;0$. For every sufficiently small $\varepsilon&gt;0$, the tail inequality $r y'\leq-(g-\varepsilon)y+g d_p+\varepsilon$ follows because $y\geq0$. Multiplying by $r^{g-\varepsilon-1}$ and integrating gives $\limsup y\leq(gd_p+\varepsilon)/(g-\varepsilon)$. Letting $\varepsilon\downarrow0$ proves the induction step. This argument uses only an upper differential inequality; no higher-order factorization-error estimate is assumed.</p>
<p>The asymptotic upper bound at order $2n-1$ gives a uniform bound for large radii. On each remaining compact interval all moments are bounded by DR1W, while $\chi_r\geq1$ and $m_2(r)/\chi_r\geq1$. Increasing $D_n$ proves the all-radius assertion.</p>
<p>This completes the upper-bound induction (I.4.19) needed for (III.5.1). Matching lower moment asymptotics, the value of the slowly varying vertex factor, and the final three-point estimates are separate conclusions. Neither a differentiable representative of a slowly varying function nor a closed higher-moment equation is needed for this upper bound.</p>


## Critical volume moments and the mass-biased limit {#section-critical-volume-equivalents}

<a id="tag-326J" data-assertion="theorem" data-title="Ordinary hydrodynamics gives every critical volume-moment equivalent"></a>
<p>Under the hypotheses of <a href="/tag/121D/">121D</a>, put $g_r=m_2(r)/\chi_r$ and $B_p(r)=\chi_r g_r^{p-1}$. For every integer $p\geq1$,</p>
<div class="math-display">$$m_p(r)\sim(2p-3)!!\,B_p(r)\qquad(r\to\infty).$$</div>
<p>Under size bias by $|K_0|$, the variable $|K_0|/g_r$ converges in law to $N^2$, where $N$ is standard normal. Moreover,</p>
<div class="math-display">$$\lim_{b\downarrow0}\sup_{r\geq1}
\frac{\mathbb E_r\min(|K_0|,b g_r)}{\chi_r}=0.$$</div>
<p>The assumptions are the critical relation $d=3\alpha$, sharp susceptibility and ordinary hydrodynamics; no spatial-moment hypothesis or restriction $\alpha&lt;2$ is needed for this assertion. Their supply by BCKB remains conditional on finite nonmonotone Reimer.</p>
<p><em>Proof.</em> Write $X=|K_0|$, $W=|K_0\cap\Lambda_r|$, $N_r=|\Lambda_r\setminus\{0\}|$, $c(r)=\beta_c|j'(r)|$ and $a(r)=c(r)N_r$. For $0\leq l\leq p-1$, the distinct-cluster comparison and Harris give</p>
<div class="math-display">$$0\leq N_r m_{l+1}m_{p-l}
-\mathbb E_r\left[X^{l+1}\sum_{y\in\Lambda_r\setminus\{0\}}
\mathbf1_{\{y\notin K_0\}}|K_y|^{p-l}\right]
\leq\mathbb E_r[X^{p+1}W].$$</div>
<p>For the lower estimate on the distinct-cluster term, apply Harris to the two increasing cluster powers and subtract the contribution from a common cluster. On that event their product is $X^{p+1}$. All expectations are finite by DR1W.</p>
<p>The upper bounds of <a href="/tag/RM79/">RM79</a> are already available at every order. Cauchy–Schwarz and the rooted window bound used in 121D therefore yield</p>
<div class="math-display">$$\mathbb E_r[X^{p+1}W]
\leq\sqrt{m_{2p+2}(r)\mathbb E_rW^2}
\leq C_p\sqrt{\chi_r g_r^{2p+1}\,r^\alpha M_r}.$$</div>
<p>Here $M_r=o(r^{2\alpha})$. Since $N_r\asymp r^{3\alpha}$, $\chi_r\asymp r^\alpha$ and $g_r=V_r\chi_r^2$, division by $N_r\chi_rB_p$ gives</p>
<div class="math-display">$$\frac{\mathbb E_r[X^{p+1}W]}{N_r\chi_rB_p}
\leq C_p V_r^{3/2}\frac{\sqrt{M_r}}{r^\alpha}=o(1).$$</div>
<p>The tree-graph inequality gives $0&lt;V_r\leq1$. This estimate uses the previously proved upper hierarchy; it does not assume the equivalent now being established.</p>
<p>For $p\geq3$, substitute the deficit bound into GG8B. The coefficients sum to $2^p-1$, a constant at fixed $p$, so</p>
<div class="math-display">$$m_p'=a\left[(p+1)\chi_r m_p+
\sum_{l=1}^{p-2}\binom pl m_{l+1}m_{p-l}\right]
+o(a\chi_rB_p)\qquad\text{a.e.}$$</div>
<p>The cases $p=1,2$ of the claimed equivalent are identities. For $p\geq3$, assume it at smaller orders and set $d_p=(2p-3)!!$. The interior sum, divided by $\chi_rB_p$, tends to $(p-2)d_p$ by the double-factorial identity 5O1G. Also 121D gives $a\chi_r=(\alpha+o(1))/r$ and $(\log B_p)'=((2p-1)\alpha+o(1))/r$. The ratio $y=m_p/B_p$ is bounded by RM79, so its equation reduces to</p>
<div class="math-display">$$r y'=-(p-2)\alpha(y-d_p)+o(1)\qquad\text{a.e.}$$</div>
<p>Put $b=(p-2)\alpha&gt;0$. Multiplying by $r^{b-1}$ and integrating shows that an error bounded by $\varepsilon$ on a tail contributes at most $\varepsilon/b$ to the limiting distance from $d_p$; the initial term decays like $r^{-b}$. Letting $\varepsilon$ tend to zero proves the induction. Local absolute continuity suffices throughout.</p>
<p>The <a href="/tag/0N85/">size-biased moment theorem</a> now applies: its $k$th moment is $m_{k+1}/(\chi_r g_r^k)\to(2k-1)!!$. If $Q_r$ denotes this normalized size-biased law, then</p>
<div class="math-display">$$\frac{\mathbb E_r\min(X,bg_r)}{\chi_r}
=\int f_b(t)\,dQ_r(t),\qquad
f_b(t)=\min\{1,b/t\},\quad f_b(0)=1.$$</div>
<p>For fixed $b&gt;0$, $f_b$ is bounded and continuous. Weak convergence and then dominated convergence as $b\downarrow0$ give zero in the iterated limit, since $\mathbb P(N^2=0)=0$. To make the estimate uniform over all $r\geq1$, first choose a tail where it is small. On the remaining compact interval, $g_r$ is bounded and $\chi_r\geq1$, so the displayed ratio is at most $b\sup g_r$. Decreasing $b$ handles that interval and cannot increase the tail bound.</p>
<p>This supplies the critical case of Proposition I.4.20 and the mass-biased volume limit needed for the three-point lower bound. It does not identify the slowly varying factor $V_r$ or assert a spatial random-measure limit.</p>


## A lower logarithmic bound for the vertex factor {#section-critical-vertex-lower}

<a id="tag-5J3U" data-assertion="theorem" data-title="The critical vertex factor cannot decay faster than the inverse square root of a logarithm"></a>
<p>Under the hypotheses of <a href="/tag/121D/">121D</a>, put $c_\chi=\alpha/\beta_c$. Then</p>
<div class="math-display">$$\liminf_{r\to\infty}\sqrt{\log r}\,V_r
\geq\frac1{\sqrt{90\alpha c_\chi^3}},\qquad
\liminf_{r\to\infty}\frac{\sqrt{\log r}}{r^{3\alpha}}m_2(r)
\geq\frac{\alpha}{\sqrt{90\beta_c^3}}.$$</div>
<p>In particular $V_r\geq c/\sqrt{\log(2+r)}$ for $r\geq1$, with a positive model-dependent constant. If also $\alpha&lt;2$, then $V_r\to0$. The lower constants are not asserted to be optimal, and these statements do not determine a logarithmic equivalent.</p>
<p><em>Proof.</em> Use the exact deficits of 121D, with $a(r)=\beta_c|j'(r)|N_r$, $N_r=|\Lambda_r\setminus\{0\}|$, $X=|K_0|$ and $W=|K_0\cap\Lambda_r|$. They satisfy</p>
<div class="math-display">$$e_1\geq0,\qquad
 e_2\leq\frac{\mathbb E_r[X^3W]}{N_r\chi_rm_2(r)}
 \leq\frac{m_4(r)}{N_r\chi_rm_2(r)}.$$</div>
<p>The fourth-moment upper bound of <a href="/tag/RM79/">RM79</a> gives $m_4(r)\leq(15+o(1))m_2(r)^3/\chi_r^2$. Consequently</p>
<div class="math-display">$$e_2-e_1\leq(15+o(1))\frac{\chi_r^3}{N_r}V_r^2.$$</div>
<p>Because $(\log V)'=3a\chi(e_1-e_2)$ exactly, the positive locally absolutely continuous function $w=V^{-2}$ satisfies</p>
<div class="math-display">$$w'=6a\chi(e_2-e_1)V^{-2}
\leq(90+o(1))\frac{a\chi_r^4}{N_r}
=\frac{90\alpha c_\chi^3+o(1)}r\qquad\text{a.e.}$$</div>
<p>Here $N_r\sim r^{3\alpha}$ and $a(r)\chi_r\sim\alpha/r$. For any $\eta&gt;0$, integration beyond a sufficiently large $r_\eta$ gives</p>
<div class="math-display">$$w(r)\leq w(r_\eta)+(90\alpha c_\chi^3+\eta)\log(r/r_\eta).$$</div>
<p>Divide by $\log r$, take the upper limit, and then let $\eta\downarrow0$. Inverting the square root proves the bound for $V$. Multiplying by $\chi_r^3/r^{3\alpha}\to c_\chi^3$ proves the bound for $m_2$. Positivity and continuity on compact intervals give the all-radius version. This argument neither assumes a sign for $V'$ nor requires the first-order errors to be logarithmically integrable.</p>
<p>For the final assertion, suppose $\alpha&lt;2$. The two-marked-vertex tail bound <a href="/tag/3M2Y/">3M2Y</a>, with its volume input supplied by RM79, lets us fix $L\geq1$ so that, for $Y_r=|K_0^r\cap\Lambda_{Lr}|$,</p>
<div class="math-display">$$m_2(r)\leq2\mathbb E Y_r^2.$$</div>
<p>Indeed $X^2-Y_r^2\leq2X(X-Y_r)$, whose expectation is at most $C m_2(r)h(L)$. Increase the cutoff from $r$ to $Lr$ and apply the rooted window estimate used in 121D at radius $Lr$. With $M_s=\widetilde M_0(s)$ this yields</p>
<div class="math-display">$$m_2(r)\leq2\mathbb E_{Lr}|K_0\cap\Lambda_{Lr}|^2
\leq C(Lr)^\alpha M_{Lr}=o(r^{3\alpha}).$$</div>
<p>Division by $\chi_r^3\asymp r^{3\alpha}$ proves $V_r\to0$. The fixed dilation is harmless; a unit-ball spatial scaling limit is not needed.</p>
<p>The first conclusion supplies the one-sided logarithmic order in Remark III.6.5, using the exact cancellation already present in the two moment equations. The second is (III.6.10). Their model assumptions are supplied conditionally on finite nonmonotone Reimer through BCKB; no new Lean proof or source-author confirmation follows.</p>

## The remaining input for the logarithmic equivalent {#section-critical-deficit-gap}

<p>The exact cancellation also specifies what is missing for a matching equivalent. In the notation above, suppose one proves, for a constant $K&gt;0$,</p>
<div class="math-display">$$e_2(r)-e_1(r)=(K+o(1))\frac{m_2(r)^2}{N_r\chi_r^3}.$$</div>
<p>Then <a href="/tag/OP8F/">OP8F</a>, with rate constant $\beta_c$, susceptibility constant $\alpha/\beta_c$ and window constant one, gives</p>
<div class="math-display">$$V_r\sim\frac{\beta_c^{3/2}}{\alpha^2\sqrt{6K\log r}},\qquad
m_2(r)\sim\frac{\alpha}{\sqrt{6\beta_c^3K}}\frac{r^{3\alpha}}{\sqrt{\log r}}.$$</div>
<p>The upper bound on $e_2-e_1$ in 5J3U supplies only one direction of this comparison. In particular, separate estimates $e_1,e_2=o(1)$ cannot identify $K$.</p>
<p>Section III.6.1 proposes to obtain this gap from the two normalized spatial deficit measures. Their needed limits, at the critical dimension, are</p>
<div class="math-display">$$\begin{aligned}
\frac1{V_r^2\chi_r^5}\sum_y\mathscr D_r^{(1)}(0,y)\,\delta_{y/r}
&\Longrightarrow\kappa^{*3}(u)\,du,\\
\frac1{V_r^3\chi_r^7}\sum_y\mathscr D_r^{(2)}(0,y)\,\delta_{y/r}
&\Longrightarrow\bigl(\kappa^{*3}(u)+2\kappa^{*4}(u)\bigr)\,du.
\end{aligned}$$</div>
<p>Here $\mathscr D^{(1)}(x,y)=\chi_r^2-\mathbb E_r[|K_x||K_y|;x\nleftrightarrow y]$ and $\mathscr D^{(2)}(x,y)=\chi_rm_2(r)-\mathbb E_r[|K_x||K_y|^2;x\nleftrightarrow y]$; both are nonnegative by the distinct-cluster comparison. The symbol $\delta_{y/r}$ denotes a unit point mass, and $\kappa$ is the probability density from the spatial scaling limit. These limits are stated here as missing inputs, not established results.</p>
<p>Once weak convergence of these finite measures is available, the unit norm ball is a continuity set because its boundary has Lebesgue measure zero. Integrating over the ball and dividing by the denominators in $e_1,e_2$ gives the gap above with $K=2\int_{\Lambda_1}\kappa^{*4}(u)\,du$, provided this constant is positive. Our window excludes the origin: its two omitted normalized contributions both equal $1/(V_r^2\chi_r^3)$ and tend to zero by 5J3U and $\chi_r\asymp r^\alpha$. Thus this convention does not change the gap constant.</p>
<p>The source first asserts polynomial moment limits in Theorem III.6.6 and then uses moment determinacy to pass to the displayed weak limits. Proving the interacting-cluster moment equations, the negligible triple-interaction error and moment determinacy remains necessary. The existing upper spatial moments and ordinary volume equivalents do not supply these steps.</p>
<p>The first normalization above uses $\chi_r^5$, as in the source's following unit-ball calculation and (III.6.15). Equation (III.6.13) instead prints $\chi_r^4$ in both the versioned HTML and PDF. The <a href="/errata/hutchcroft-lrp-3/">errata record</a> marks the discrepancy provisionally; it does not certify the proposed limit or declare the final logarithmic theorem false.</p>


## Tightness of the normalized deficit measures {#section-critical-deficit-tightness}

<a id="tag-GL6S" data-assertion="proposition" data-title="Critical deficit measures have uniform spatial tails and polynomial moments"></a>
<p>Under the hypotheses of 7GBI, let $\mu_{1,r}$ and $\mu_{2,r}$ be the two normalized deficit measures in the preceding section, with denominators $V_r^2\chi_r^5$ and $V_r^3\chi_r^7$, respectively. They are finite nonnegative measures. For every integer $q\geq0$ there are $C_q&lt;\infty$ and a positive function $h_q(T)$ decaying faster than every inverse power as $T\to\infty$, such that, for $i=1,2$,</p>
<div class="math-display">$$\sup_{r\geq1}\int\|u\|^q\,d\mu_{i,r}(u)\leq C_q,\qquad
\sup_{r\geq1}\int_{\|u\|\geq T}\|u\|^q\,d\mu_{i,r}(u)\leq C_qh_q(T)
\quad(T\geq1).$$</div>
<p>Use $\|u\|^0=1$, including at zero. Each family is relatively compact for weak convergence of finite measures, and along a weakly convergent subsequence every polynomial integral also converges. The limiting measures are not identified by these bounds.</p>
<p><em>Proof.</em> Write $X=|K_0|$ and $X_y=|K_y|$. For $k=1,2$, the distinct-cluster comparison and Harris imply</p>
<div class="math-display">$$0\leq\mathscr D_r^{(k)}(0,y)
\leq\mathbb E_r[X X_y^k;0\leftrightarrow y]
=\mathbb E_r[X^{k+1}\mathbf1_{\{y\in K_0\}}].$$</div>
<p>For the upper bound, decompose $\mathbb E_r[XX_y^k]$ according to whether the roots are connected and use $\mathbb E_r[XX_y^k]\geq\mathbb E_rX\,\mathbb E_rX_y^k$. The lower bound is <a href="/tag/1AC7/">1AC7</a>. Thus, for every nonnegative weight $f$ on the lattice, Tonelli gives</p>
<div class="math-display">$$\sum_y\mathscr D_r^{(k)}(0,y)f(y)
\leq\mathbb E_r\left[X^{k+1}\sum_{y\in K_0}f(y)\right].$$</div>
<p>For $f(y)=\|y\|^q$ the right side is a mixed moment with $k+2$ marked vertices: one carries degree $q$ and the other $k+1$ carry degree zero. Apply <a href="/tag/AR3F/">AR3F</a>, whose volume input is supplied by RM79. The bound is</p>
<div class="math-display">$$C_q V_r^{k+1}r^{(2k+3)\alpha+q}
\asymp C_q V_r^{k+1}\chi_r^{2k+3}r^q.$$</div>
<p>For $f(y)=\|y\|^q\mathbf1_{\{\|y\|\geq Tr\}}$, <a href="/tag/3M2Y/">3M2Y</a> gives the same expression multiplied by a rapidly decaying $h_q(T)$. Alternatively, its tail proof applies by increasing the degree of this one marked vertex. Divide by $V_r^{k+1}\chi_r^{2k+3}r^q$ to obtain both assertions. This also proves finiteness of the measures without an unweighted countable sum of susceptibility bounds.</p>
<p>The case $q=0$ gives bounded total mass and uniform tightness, hence weak relative compactness. If $\mu_{i,r_j}\Longrightarrow\mu$, the moment bound of any degree higher than that of a polynomial $P$ gives uniform integrability of $P$. Apply weak convergence to $P$ multiplied by a continuous compactly supported cutoff, then let the cutoff radius tend to infinity. The same moment bound passes to $\mu$ by truncation, so both tails vanish and $\int P\,d\mu_{i,r_j}\to\int P\,d\mu$.</p>
<p>This proves the critical case of Lemma III.6.9 and the accompanying tightness step. To deduce the weak limits required above, one must still compute the limiting polynomial moments and show that they determine the proposed convolution measures. Tightness alone supplies neither uniqueness nor their normalization constants.</p>


## Exact derivatives of the two-root deficits {#section-two-root-deficit-derivatives}

<a id="tag-B5NA" data-assertion="theorem" data-title="The two-root deficit derivatives separate third-cluster growth from root-cluster mergers"></a>
<p>Retain the radial model of <a href="/tag/DR1W/">DR1W</a>, assume $j$ is continuously differentiable, and work at intensity $\beta_c$. Fix $y\in\mathbb Z^d$, allowing $y=0$. Write $X=|K_0|$, $Y=|K_y|$, $Z_z=|K_z|$, $\chi=\mathbb E_rX$, $m_2=\mathbb E_rX^2$, and</p>
<div class="math-display">$$B_r=\{z:0&lt;\|z\|\leq r\},\qquad c(r)=\beta_c|j'(r)|,\qquad
I_z=\mathbf1_{\{y\notin K_0\cup K_z\}}.$$</div>
<p>All clusters in the following sums are at cutoff $r$. For a random function $F$ on the vertices put</p>
<div class="math-display">$$\mathcal S_r(F)=\sum_{x\in K_0}\sum_{z\in x+B_r}
\mathbf1_{\{z\notin K_0\}}F(z),\qquad
J_k(r,y)=\mathbf1_{\{0\nleftrightarrow y\}}
\sum_{x\in K_0}\sum_{z\in K_y}\mathbf1_{\{z-x\in B_r\}}XY^k.$$</div>
<p>The functions $r\mapsto\mathscr D_r^{(1)}(0,y)$ and $r\mapsto\mathscr D_r^{(2)}(0,y)$ are locally absolutely continuous on $(0,\infty)$. Almost everywhere,</p>
<div class="math-display">$$\begin{aligned}
\frac d{dr}\mathscr D_r^{(1)}(0,y)
&=c(r)\left[2\mathbb E_r\mathcal S_r\bigl(Z_z(\chi-I_zY)\bigr)
+\mathbb E_rJ_1(r,y)\right],\\
\frac d{dr}\mathscr D_r^{(2)}(0,y)
&=c(r)\Bigl[\mathbb E_r\mathcal S_r\bigl((Z_z^2+2XZ_z)(\chi-I_zY)\bigr)\\
&\hspace{38mm}+\mathbb E_r\mathcal S_r\bigl(Z_z(m_2-I_zY^2)\bigr)
+\mathbb E_rJ_2(r,y)\Bigr].
\end{aligned}$$</div>
<p>Every expectation is absolutely integrable on compact radius intervals. Keeping the factor $c(r)$ multiplicatively includes flat portions of the kernel. These identities require neither $d=3\alpha$, $\alpha&lt;2$ nor hydrodynamics.</p>
<p><em>Proof.</em> First work in a finite induced graph and apply the Poisson opening generator to $Q_{1,k}=XY^k\mathbf1_{\{0\nleftrightarrow y\}}$. When the roots are already connected, this observable and all its future increments are zero. Otherwise an opening can grow one root component by a third component, join the two root components, or leave the observable unchanged. If the third component has size $z$, the two growth increments are $zY^k$ and $X[(Y+z)^k-Y^k]$. A root-component merger removes $XY^k$; its edges are counted once, from $K_0$ to $K_y$.</p>
<p>We justify passage to the countable model before collecting symmetric terms. Fix a compact radius interval $[a,R]\subset(0,\infty)$. The cutoff-$R$ model dominates every configuration under consideration and has all volume moments finite by DR1W. Its edges have length at most $R$. Hence, for every integer $p\geq1$,</p>
<div class="math-display">$$\mathbb P_R(0\leftrightarrow v)
\leq C_{p,R}(1+\|v\|)^{-p}.$$</div>
<p>A connection to $v$ needs a simple path with at least $\|v\|/R$ edges and therefore at least that many vertices; Markov's inequality for $|K_0^R|^p$ gives the estimate. The same bound holds from the other root.</p>
<p>The absolute generator contributions are bounded by sums over an endpoint $x$ in one of the two root clusters and a second endpoint within the finite displacement set $B_R$. Their weights are polynomials of bounded degree in the sizes of at most three clusters. Cauchy–Schwarz for the root-connection indicator, followed by Hölder for the cluster-size factors, bounds each expectation by a constant times $\mathbb P_R(0\leftrightarrow x)^{1/2}$ or $\mathbb P_R(y\leftrightarrow x)^{1/2}$. Choosing $p&gt;2d$ makes their sums over $x$ finite. These bounds are uniform in the finite box and in $r\in[a,R]$; the rate $c$ is bounded on this interval. The observables themselves are dominated by an integrable product of cutoff-$R$ cluster sizes.</p>
<p>In an increasing finite-box exhaustion, every fixed collection of cutoff-$R$ root clusters eventually agrees with its finite-box counterpart. Dominated convergence therefore passes the integrated finite generator identity to the full model, including its positive and negative terms. The result is a locally absolutely continuous function with the stated generator as its a.e. derivative. This argument does not differentiate a pointwise limit without controlling the generator.</p>
<p>Now use the reflection $v\mapsto y-v$, which preserves the radial law and exchanges the two roots. For $k=1$ the two third-cluster growth terms have equal expectations. For $k=2$ reflection turns growth of $K_y$ into the term involving $(Z_z^2+2XZ_z)Y$. Thus</p>
<div class="math-display">$$\begin{aligned}
\frac d{dr}\mathbb E_rQ_{1,1}
&=c(r)\left[2\mathbb E_r\mathcal S_r(I_zZ_zY)-\mathbb E_rJ_1(r,y)\right],\\
\frac d{dr}\mathbb E_rQ_{1,2}
&=c(r)\left[\mathbb E_r\mathcal S_r(I_zZ_zY^2)
+\mathbb E_r\mathcal S_r\bigl(I_z(Z_z^2+2XZ_z)Y\bigr)
-\mathbb E_rJ_2(r,y)\right].
\end{aligned}$$</div>
<p>The indicator in $\mathcal S_r$, together with $I_z$, says exactly that $0,y,z$ are in three distinct clusters. The single-root generator gives</p>
<div class="math-display">$$\chi'=c(r)\mathbb E_r\mathcal S_r(Z_z),\qquad
m_2'=c(r)\mathbb E_r\mathcal S_r(2XZ_z+Z_z^2).$$</div>
<p>Apply the product rule to $\mathscr D^{(1)}=\chi^2-\mathbb E Q_{1,1}$ and $\mathscr D^{(2)}=\chi m_2-\mathbb E Q_{1,2}$, and subtract the displayed derivatives of the two distinct-root expectations. This gives the claimed formulas. If $y=0$, then $I_z=0$ and $J_k=0$, so the same identities reduce to the derivatives of $\chi^2$ and $\chi m_2$.</p>
<p>This supplies Lemma III.6.10 with the countable limiting argument and possible vanishing rate included. The bracketed third-cluster terms are exact expectations; replacing them by pair interactions with a negligible error is the separate content of Lemma III.6.11.</p>

## The total mass of the merging terms {#section-critical-merging-mass}

<a id="tag-HV5B" data-assertion="theorem" data-title="Critical unweighted merging terms factorize with a vanishing relative error"></a>
<p>Under the hypotheses of <a href="/tag/7GBI/">7GBI</a>, let $J_k(r,y)$ be as above and put $N_r=|B_r|$. For every fixed integer $k\geq1$, the total merging term is finite and satisfies</p>
<div class="math-display">$$\mathcal M_k(r):=\sum_y\mathbb E_rJ_k(r,y)
=\mathbb E_r\sum_{z\in B_r}\mathbf1_{\{0\nleftrightarrow z\}}X^2|K_z|^{k+1},$$</div>
<div class="math-display">$$0\leq N_rm_2(r)m_{k+1}(r)-\mathcal M_k(r)
\leq m_{k+4}(r).$$</div>
<p>In particular, as $r\to\infty$,</p>
<div class="math-display">$$\mathcal M_k(r)\sim N_rm_2(r)m_{k+1}(r)
\sim(2k-1)!!\,N_rV_r^{k+1}\chi_r^{2k+4}.$$</div>
<p>Thus the unweighted merging terms for the two deficit derivatives have respective equivalents $N_rV_r^2\chi_r^6$ and $3N_rV_r^3\chi_r^8$. This is the degree-zero part of Lemma III.6.12; no spatial convolution limit is assumed.</p>
<p><em>Proof.</em> Sum first over $y$ in the definition of $J_k$. Whenever $z\notin K_0$, all choices $y\in K_z$ have the same cluster size, giving</p>
<div class="math-display">$$\mathcal M_k
=\mathbb E_r\sum_{x\in K_0}\sum_{z\in x+B_r}
\mathbf1_{\{z\notin K_0\}}X|K_z|^{k+1}.$$</div>
<p>Send the summand from the marked root to $x$. The translation-invariant mass-transport identity replaces the sum over $x\in K_0$ by a factor $X$ at the receiving root and leaves $z$ in $B_r$. This proves the stated identity. Tonelli permits both operations before finiteness is known.</p>
<p>Apply <a href="/tag/1AC7/">the distinct-cluster comparison</a> to the powers $X^2$ and $|K_z|^{k+1}$. Harris bounds their full product expectation below by $m_2m_{k+1}$, and their common-cluster contribution is $\mathbb E_r[X^{k+3};z\in K_0]$. Summing gives</p>
<div class="math-display">$$0\leq N_rm_2m_{k+1}-\mathcal M_k
\leq\mathbb E_r\left[X^{k+3}|K_0\cap B_r|\right]
\leq m_{k+4}.$$</div>
<p>The product upper bound makes $\mathcal M_k$ finite. The volume equivalents of <a href="/tag/326J/">326J</a> give</p>
<div class="math-display">$$\frac{m_{k+4}}{N_rm_2m_{k+1}}
\sim\frac{(2k+5)!!}{(2k-1)!!}\,\frac{\chi_r^3}{N_r}V_r^2
\longrightarrow0.$$</div>
<p>Indeed $\chi_r^3/N_r\to(\alpha/\beta_c)^3$ and <a href="/tag/5J3U/">5J3U</a> gives $V_r\to0$ when $\alpha&lt;2$. This proves the factorization and its coefficient. In particular, the factors one and three are volume-moment coefficients; their derivation does not require the spatially weighted part of the source lemma.</p>
<p>The critical hydrodynamic input retains its finite nonmonotone Reimer dependency. The exact identities B5NA and the unweighted merging equivalents here leave the third-cluster approximation and the nonconstant spatial weights as remaining steps toward the deficit-measure limits.</p>


## Spatially weighted merging terms {#section-critical-weighted-mergers}

<a id="tag-J2QW" data-assertion="theorem" data-title="Critical spatial merging terms converge to the four- and five-edge convolutions"></a>
<p>Under the hypotheses of <a href="/tag/7GBI/">7GBI</a>, use $J_k(r,y)$ from <a href="/tag/B5NA/">B5NA</a>, $N_r=|B_r|$, and the unit-volume norm ball $B$. Let $\kappa$ be the jump density in <a href="/tag/AL0I/">AL0I</a>. For every real polynomial $P$ on $\mathbb R^d$,</p>
<div class="math-display">$$\begin{aligned}
\frac{\sum_y\mathbb E_rJ_1(r,y)P(y/r)}{N_rV_r^2\chi_r^6}
&\longrightarrow\int[\kappa^{*4}*\mathbf1_B](u)P(u)\,du,\\
\frac{\sum_y\mathbb E_rJ_2(r,y)P(y/r)}{N_rV_r^3\chi_r^8}
&\longrightarrow\int[(\kappa^{*4}+2\kappa^{*5})*\mathbf1_B](u)P(u)\,du.
\end{aligned}$$</div>
<p>Every sum and integral is absolutely convergent. For a homogeneous monomial of degree $p$, one may equivalently put $P(y)$ in the numerator and multiply the denominator by $r^p$. The statements allow signed and zero limiting moments.</p>
<p><em>Proof.</em> Summing the cluster containing $y$ and then transporting the root to the joining endpoint, as in <a href="/tag/HV5B/">HV5B</a>, gives for $k=1,2$</p>
<div class="math-display">$$\sum_y\mathbb E_rJ_k(r,y)P(y/r)
=\mathbb E_r\sum_{h\in B_r}\mathbf1_{\{0\nleftrightarrow h\}}
|K_0||K_h|^k\sum_{x\in K_0}\sum_{z\in K_h}P((z-x)/r).$$</div>
<p>These changes of variables are valid first with absolute weights; the bounds below prove their summability. Replace the two distinct clusters by independent clusters $K,K'$ rooted at zero. The resulting expression is</p>
<div class="math-display">$$\mathcal A_k(P)=\sum_{h\in B_r}\mathbb E_r\left[|K||K'|^k
\sum_{x\in K}\sum_{z\in K'}P((h+z-x)/r)\right].$$</div>
<p>Expand the cluster-volume factors into marked vertices, keeping the polynomial weight intact. For each fixed set of marks, the same BK–Harris comparison as in YHNS bounds the absolute factorization error by</p>
<div class="math-display">$$\mathbb E_r\left[|K_0|^{k+2}\sum_{x,z\in K_0}|P((z-x)/r)|\right]
\leq C_PV_r^{k+3}\chi_r^{2k+7}.$$</div>
<p>For the first inequality, the common-cluster error has a mark at $h$; summing it over $B_r$ is at most one additional cluster-volume factor. For the second, a monomial of degree $p$ is bounded by $C r^{-p}(\|x\|^p+\|z\|^p)$, with the constant monomial treated separately. Apply AR3F with $k+4$ cluster marks and its volume premise from RM79, then use $\chi_r\asymp r^\alpha$. For a general polynomial sum over its finitely many homogeneous terms. The ratio of this error to $N_rV_r^{k+1}\chi_r^{2k+4}$ is $O(V_r^2\chi_r^3/N_r)=o(1)$.</p>
<p>It remains to compute the independent product. AL0I gives the polynomial limits of the finite measures</p>
<div class="math-display">$$\nu_{j,r}(f)=\frac{\mathbb E_r[|K_0|^{j-1}\sum_{x\in K_0}f(x/r)]}{V_r^{j-1}\chi_r^{2j-1}}.
$$</div>
<p>For $j=2$ their limiting density is $\kappa^{*2}$: the single three-leaf tree has two edges between the root and the marked leaf. For $j=3$ the density is $\kappa^{*2}+2\kappa^{*3}$: among the three four-leaf trees, the root and marked leaf form a pair on one tree and are separated by three edges on the other two. Integrating every unweighted leaf branch gives one in each case. Thus</p>
<div class="math-display">$$\nu_{2,r}(f)\longrightarrow\int f\kappa^{*2},\qquad
\nu_{3,r}(f)\longrightarrow\int f(\kappa^{*2}+2\kappa^{*3})$$</div>
<p>for every polynomial $f$. Also $N_r^{-1}\sum_{h\in B_r}\delta_{h/r}$ converges in all polynomial moments to the uniform law $\mathbf1_B(u)\,du$. Expanding $P(u+z-x)$ into a finite sum of products of polynomials in $u,z,x$ therefore identifies the limit of $\mathcal A_k(P)$ after normalization as the convolution of this uniform law with the two limiting cluster measures. The first cluster law is even, so the minus sign on $x$ does not change it. The two resulting densities are precisely those in the statement. This proves both limits.</p>
<p>This completes the critical, $\alpha&lt;2$ version of Lemma III.6.12 using the single-cluster spatial limit rather than assuming it. At $P=1$ the integrals are one and three, agreeing with HV5B. Neither the triple-interaction estimate nor the unresolved interception reduction is used.</p>


## What the deficit moment equations imply {#section-conditional-deficit-moments}

<a id="tag-ENWJ" data-assertion="theorem" data-title="The two triangular deficit equations determine all polynomial limits"></a>
<p>Assume the critical hypotheses of <a href="/tag/7GBI/">7GBI</a>, and use the jump density $\kappa$ of <a href="/tag/AL0I/">AL0I</a>. Let $B$ be the closed unit norm ball, of volume one. For a polynomial $P$, put</p>
<div class="math-display">$$F_i(P;r)=\sum_y\mathscr D_r^{(i)}(0,y)P(y),\qquad
h_1=V_r^2\chi_r^5,\quad h_2=V_r^3\chi_r^7,\quad b_r=V_r\chi_r^2=h_2/h_1,$$</div>
<div class="math-display">$$k_j(P)=\int\kappa^{*j}(u)P(u)\,du,\qquad
a_j(P)=\int[\kappa^{*j}*\mathbf1_B](u)P(u)\,du.$$</div>
<p>For a monomial $P=\prod_{t=1}^p\ell_t$, keep the linear factors labelled and write $P_I=\prod_{t\in I}\ell_t$, with $P_\varnothing=1$. Sums below run over proper subsets $I\subsetneq[p]$; this counts repeated factors with their multiplicities without dividing polynomials at their zeros.</p>
<p><strong>Additional hypothesis.</strong> For every such monomial, the two functions $F_i(P;\cdot)$ are locally absolutely continuous and satisfy, almost everywhere for large $r$,</p>
<div class="math-display">$$\begin{aligned}
r\partial_rF_1(P;r)
&=4\alpha F_1(P;r)
+2\alpha\sum_{I\subsetneq[p]}a_1(P_{I^c})r^{p-|I|}F_1(P_I;r)\\
&\quad+\alpha a_4(P)h_1r^p+o(h_1r^p),\\
r\partial_rF_2(P;r)
&=5\alpha F_2(P;r)+3\alpha b_rF_1(P;r)\\
&\quad+2\alpha\sum_{I\subsetneq[p]}a_1(P_{I^c})r^{p-|I|}F_2(P_I;r)\\
&\quad+2\alpha b_r\sum_{I\subsetneq[p]}a_2(P_{I^c})r^{p-|I|}F_1(P_I;r)\\
&\quad+\alpha\bigl(a_4(P)+2a_5(P)\bigr)h_2r^p+o(h_2r^p).
\end{aligned}$$</div>
<p>Each remainder is bounded in absolute value by $\eta_{i,P}(r)h_ir^p$ outside a null set, for a locally bounded measurable $\eta_{i,P}\to0$. This hypothesis is the remaining probabilistic input; it is not inferred from the single-cluster spatial limits or the merger estimates alone.</p>
<p>Then, for every monomial $P$ of degree $p$,</p>
<div class="math-display">$$\frac{F_1(P;r)}{h_1r^p}\longrightarrow k_3(P),\qquad
\frac{F_2(P;r)}{h_2r^p}\longrightarrow k_3(P)+2k_4(P).$$</div>
<p>Equivalently, the normalized deficit measures have these limits against every polynomial evaluated at $y/r$. In particular their total masses tend to one and three.</p>
<p><em>Proof.</em> All the integrals and sums defining the moments are finite by the exponential moments of the resolvent and <a href="/tag/GL6S/">GL6S</a>. By <a href="/tag/121D/">121D</a>, $h_1r^p$ and $h_2r^p$ are regularly varying with respective indices $5\alpha+p$ and $7\alpha+p$.</p>
<p>Induct first on $p$ in the first equation. If the normalized lower moments have limits $c_1(P_I)$, its forcing divided by $h_1r^p$ tends to a constant. The gap between the forcing index and the homogeneous coefficient is $\alpha+p&gt;0$. The signed ODE theorem <a href="/tag/2KB9/">2KB9</a> therefore gives a limit $c_1(P)$ determined by</p>
<div class="math-display">$$(\alpha+p)c_1(P)=2\alpha\sum_{I\subsetneq[p]}a_1(P_{I^c})c_1(P_I)+\alpha a_4(P).$$</div>
<p>This also starts the induction at $p=0$, where the sum is empty and $c_1(1)=1$. To identify the coefficients, use the chain case of the edge-insertion identity <a href="/tag/IX97/">IX97</a>:</p>
<div class="math-display">$$(p+j\alpha)k_j(P)=j\alpha a_{j+1}(P).$$</div>
<p>Indeed a chain of $j$ independent resolvent increments has density $\kappa^{*j}$, and replacing any one edge as in IX97 gives density $\kappa^{*(j+1)}*\mathbf1_B$. The polynomial addition formula gives</p>
<div class="math-display">$$\sum_{I\subsetneq[p]}a_1(P_{I^c})k_3(P_I)=a_4(P)-k_3(P).$$</div>
<p>Substitution reduces the recurrence to $(p+3\alpha)k_3(P)=3\alpha a_4(P)$. Its unique solution is therefore $c_1=k_3$.</p>
<p>Now induct on degree in the second equation, with the first limits already known. The identity $b_rh_1=h_2$ puts every first-deficit term on the same scale as the second forcing. The positive gap is $2\alpha+p$, so another application of 2KB9 gives</p>
<div class="math-display">$$\begin{aligned}
(2\alpha+p)c_2(P)
&=3\alpha k_3(P)+2\alpha\sum_{I\subsetneq[p]}a_1(P_{I^c})c_2(P_I)\\
&\quad+2\alpha\sum_{I\subsetneq[p]}a_2(P_{I^c})k_3(P_I)
+\alpha\bigl(a_4(P)+2a_5(P)\bigr).
\end{aligned}$$</div>
<p>At degree zero this gives $c_2(1)=3$. For the proposed solution $c_2=k_3+2k_4$, the two proper-subset sums are respectively $a_4+2a_5-k_3-2k_4$ and $a_5-k_3$, evaluated at $P$. The recurrence becomes</p>
<div class="math-display">$$(p+3\alpha)k_3(P)+2(p+4\alpha)k_4(P)
=3\alpha a_4(P)+8\alpha a_5(P),$$</div>
<p>which is the sum of the chain identities for $j=3$ and $j=4$. This proves the second limit. All arguments use additive errors and the signed ODE theorem, so zero or negative limiting moments require no separate division. A finite expansion into homogeneous monomials proves the polynomial formulation.</p>
<p>The reflection $y\mapsto-y$ leaves both deficit functions unchanged. Thus source terms written with $P_I(-y)$ have the same summed moments as those above. The forcing terms here agree with <a href="/tag/J2QW/">J2QW</a> and the later proof of Theorem III.6.6. The statement of Lemma III.6.13 instead prints $a_3$ in the first equation and $3a_4$ in the second, in both HTML and PDF. The <a href="/errata/hutchcroft-lrp-3/">provisional erratum</a> records this discrepancy. For a nonzero linear form $\ell$, $a_4(\ell^2)-a_3(\ell^2)=k_1(\ell^2)&gt;0$ and $a_4(\ell^2)+2a_5(\ell^2)-3a_4(\ell^2)=2k_1(\ell^2)&gt;0$. Here $k_1(\ell^2)=\alpha(2-\alpha)^{-1}\int_B\ell(u)^2\,du&gt;0$ by the one-edge identity, so the differences cannot be hidden in vanishing errors. Establishing the two displayed equations for the actual deficit moments still requires the unresolved triple-interaction argument.</p>

## Conditional weak limits and the logarithmic amplitude {#section-conditional-deficit-amplitude}

<a id="tag-RDLW" data-assertion="corollary" data-title="The deficit equations imply weak convergence and the critical logarithmic amplitude"></a>
<p>Under the hypotheses of ENWJ, including its two additional deficit equations,</p>
<div class="math-display">$$\mu_{1,r}\Longrightarrow\kappa^{*3}(u)\,du,\qquad
\mu_{2,r}\Longrightarrow\bigl(\kappa^{*3}(u)+2\kappa^{*4}(u)\bigr)\,du,$$</div>
<p>where $\mu_{i,r}=h_i^{-1}\sum_y\mathscr D_r^{(i)}(0,y)\delta_{y/r}$. Put</p>
<div class="math-display">$$K=2\int_B\kappa^{*4}(u)\,du.$$</div>
<p>Then $0&lt;K\leq2$, and</p>
<div class="math-display">$$V_r\sim\frac{\beta_c^{3/2}}{\alpha^2\sqrt{6K\log r}},\qquad
m_2(r)\sim\frac{\alpha}{\sqrt{6\beta_c^3K}}\frac{r^{3\alpha}}{\sqrt{\log r}}.$$</div>
<p><em>Proof.</em> GL6S supplies relative compactness of the nonnegative finite measures and convergence of all polynomial integrals along any weakly convergent subsequence. ENWJ identifies those integrals with the proposed densities. These finite measures have an exponential moment near zero, since the same is true of $\kappa$ and hence of its finite convolutions.</p>
<p>Their moments determine them. To see this for any competing finite measure, expand $\cosh(t\ell(u))$ into its nonnegative even-power series. Equality of moments and Tonelli give finiteness and equality of these integrals for small $t$. The moment generating functions of all one-dimensional projections then agree near zero. Normalize by the common total mass, which is one or three, and apply uniqueness of the one-dimensional laws and Cramér–Wold. Thus every weak subsequential limit is the stated measure, proving convergence of the full families.</p>
<p>The norm ball is a continuity set because its boundary is Lebesgue-null. Consequently</p>
<div class="math-display">$$\mu_{2,r}(B)-\mu_{1,r}(B)\longrightarrow K.$$</div>
<p>The exact moment deficits of 121D, with $N_r=|B_r|$, can be written</p>
<div class="math-display">$$e_1=\frac{\sum_{y\in B_r}\mathscr D_r^{(1)}(0,y)}{N_r\chi_r^2},\qquad
e_2=\frac{\sum_{y\in B_r}\mathscr D_r^{(2)}(0,y)}{N_r\chi_rm_2(r)}.$$</div>
<p>Here $B_r$ excludes the origin. But both normalized measures have exactly the same atom there:</p>
<div class="math-display">$$\mu_{1,r}(\{0\})=\mu_{2,r}(\{0\})=\frac1{V_r^2\chi_r^3}.$$</div>
<p>It cancels from their difference, so no separate bound on that atom is needed. Therefore</p>
<div class="math-display">$$e_2-e_1=\frac{V_r^2\chi_r^3}{N_r}\bigl(\mu_{2,r}(B)-\mu_{1,r}(B)\bigr)
=(K+o(1))\frac{m_2(r)^2}{N_r\chi_r^3}.$$</div>
<p>The constant is finite because $\kappa^{*4}$ is a probability density. For positivity, choose a nonzero bounded even function $f\leq\kappa$ with bounded support. Then $f\in L^2$, and $f*f$ is continuous with value $\int f^2&gt;0$ at zero. Its self-convolution is positive near zero and is bounded above by $\kappa^{*4}$. Thus the integral over $B$ is positive.</p>
<p>Apply <a href="/tag/OP8F/">OP8F</a> to the exact two moment equations with rate constant $a_0=\beta_c$, susceptibility constant $c=\alpha/\beta_c$, and window constant $\nu=1$. These constants follow from $\beta_c|j'(r)|N_r\sim\beta_c r^{-\alpha-1}$, $\chi_r\sim cr^\alpha$ and $N_r\sim r^{3\alpha}$. Substitution gives the two displayed equivalents.</p>
<p>This completes the analytic passage from the explicit deficit equations to the weak limits and logarithmic coefficient. It remains a conditional conclusion: the coupling, cut-event, interception and final decoupling estimates needed to establish those equations have not been replaced by the single-cluster results.</p>


## Changing the root of a triple interaction {#section-triple-root-transport}

<a id="tag-JG0C" data-assertion="proposition" data-title="Triple interactions have an exact transported target-tuple representation"></a>
<p>Let $\mathbb P$ be a translation-invariant independent bond law on $\mathbb Z^d$. Assume that</p>
<div class="math-display">$$\mathbb E\left[|K_0|^k\sum_{v\in K_0}(1+\|v\|^s)\right]&lt;\infty
\qquad(k,s\geq0\text{ integers}).$$</div>
<p>Fix a finite symmetric set $W=-W$, integers $p_1\geq0$, $p_2,n\geq1$, and a polynomial $P$. Write $X_v=|K_v|$, $m_n=\mathbb EX_0^n$, and define the sum of expectations</p>
<div class="math-display">$$\mathcal I(P)=\sum_y P(y)\,
\mathbb E\!\left[\sum_{u\in K_0}\sum_{v\in u+W}
\mathbf1_{\{v\notin K_0\}}X_0^{p_1}X_v^{p_2}
\bigl(m_n-\mathbf1_{\{y\notin K_0\cup K_v\}}X_y^n\bigr)\right].$$</div>
<p>Then</p>
<div class="math-display">$$\begin{aligned}
\mathcal I(P)=\sum_{x\in W}\sum_{z,y}P(y-z)\,
\mathbb E\!\left[\mathbf1_{\{x\notin K_0,\ z\in K_x\}}X_0^{p_2}X_x^{p_1}
\bigl(m_n-\mathbf1_{\{y\notin K_0\cup K_x\}}X_y^n\bigr)\right].
\end{aligned}$$</div>
<p>For each $x,y$, take the independent copies of <a href="/tag/DR5Q/">DR5Q</a>, with $A=K_0(\omega_0)$, $B=K_x(\omega_x|_{A^c})$, $C=K_x(\omega_x)$, $H=K_y(\omega_y)$ and $H_S=K_y(\omega_y|_{S^c})$, empty when $y\in S$. Equivalently,</p>
<div class="math-display">$$\mathcal I(P)=\sum_{x\in W}\sum_{z,y}P(y-z)\,
\mathbf E\!\left[\mathbf1_{\{x\notin A,\ z\in B\}}|A|^{p_2}|B|^{p_1}
\bigl(|H|^n-|H_{A\cup B}|^n\bigr)\right].$$</div>
<p>Both series of integrated coefficients are absolutely summable after multiplication by the displayed polynomial. They do not require summing a centered random field before taking expectation.</p>
<p><em>Proof.</em> For fixed $u,v,y$ in the first expression, use DR5Q with roots $0,v,y$. The nonnegative weight involving the first two retained clusters is independent of the original third copy. Replacing the constant $m_n$ by its independent realization $|H|^n$ therefore expresses that expected coefficient as an expectation of a nonnegative loss. Thus Tonelli applies to arbitrary nonnegative test functions of the marked vertices.</p>
<p>Translate the configuration by $-v$ and make the change of variables</p>
<div class="math-display">$$x=u-v,\qquad z=-v,\qquad y'=y-v.$$</div>
<p>Symmetry of $W$ gives $x\in W$. The old vertices $0,u$ lie in one cluster, so the new vertices $z,x$ do also; their cluster can be rooted at $x$. The old cluster at $v$ becomes the root cluster. Consequently its exponent is $p_2$, the other retained cluster's exponent is $p_1$, and $P(y)=P(y'-z)$. Translation invariance and renaming $y'$ give the first identity.</p>
<p>Apply DR5Q once more at roots $0,x,y$. On $x\notin A$, the second assembled cluster is $B$, and the surviving third cluster off $A\cup B$ is $H_{A\cup B}$. The variables $A,B$ depend only on the first two copies. Averaging the independent $|H|^n$ replaces $m_n$ and proves the second identity.</p>
<p>It remains to justify signed polynomial tests. For $S=A\cup B$,</p>
<div class="math-display">$$0\leq |H|^n-|H_S|^n
\leq |H|^n\mathbf1_{\{H\cap S\ne\varnothing\}}
\leq\sum_{w\in S}|H|^n\mathbf1_{\{w\in H\}}.$$</div>
<p>If $s=\deg P$, then $|P(y-z)|\leq C_P(1+\|y-w\|^s+\|w\|^s+\|z\|^s)$. For fixed $w$, translation invariance gives</p>
<div class="math-display">$$\sum_y\mathbb E[|K_y|^n\mathbf1_{\{w\in K_y\}}]=m_{n+1},\qquad
\sum_y\|y-w\|^s\mathbb E[|K_y|^n\mathbf1_{\{w\in K_y\}}]
=\mathbb E\left[X_0^n\sum_{v\in K_0}\|v\|^s\right].$$</div>
<p>Now use $B\subseteq C$ and $S\subseteq A\cup C$. Summing the remaining marks $z,w$ leaves only polynomial volume and spatial moments of the first two independent clusters. They are finite by hypothesis, and $x$ ranges over a fixed finite set. This proves absolute summability and hence the identities for signed $P$.</p>
<p>The third-cluster loss also has the exact tuple expansion</p>
<div class="math-display">$$|H|^n-|H_S|^n
=\sum_{(a_1,\ldots,a_n)\in H^n}
\mathbf1_{\{a_k\notin H_S\text{ for some }k\}}.$$</div>
<p>At a critical cutoff, the moment hypothesis follows from AR3F and RM79. With $W=B_r$, this is the exact change of root preceding III.6.34. For the source triples $(p_1,p_2,p_3)=(0,1,1),(0,2,1),(1,1,1)$, the transported root powers $(i,j)$ are $(1,0),(2,0),(1,1)$. The redundancy and joint-cut estimates <a href="/tag/DVHL/">DVHL</a> and <a href="/tag/CWM1/">CWM1</a> therefore have precisely the source error scale in all three cases.</p>
<p>For $(0,1,2)$ the same exact transport holds, but the loss concerns ordered pairs of targets. Two single cuts may remove different coordinates of a pair. DVHL controls the same-target redundancy contribution, while <a href="/tag/6IJQ/">6IJQ</a> controls the different-target contribution using two original geodesics. The joint-cut estimate with an extra third-cluster power, interception and final decoupling remain separate obligations.</p>


## Cut estimates for every transported power {#section-transported-power-cuts}

<p>The different-coordinate redundancy term left open after JG0C is controlled by <a href="/tag/6IJQ/">6IJQ</a>. The joint-cut estimate <a href="/tag/B9Z5/">B9Z5</a> now also handles every target-tuple power, retaining the extra third-cluster factor within the disjoint-witness expectation. With the transported powers $i=p_2$, $j=p_1$, $m=p_3$, its error has relative order $O(V_r^2)$ on the source scale $|B_r|V_r^{p_1+p_2+p_3}r^s\chi_r^{2(p_1+p_2+p_3)+2}$. Thus all four power triples used in III.6.10 have both cut estimates. Interception and final decoupling remain unresolved, so the ODE assumptions of ENWJ and the conditional conclusion RDLW are unchanged.</p>



## Decoupling the two single-cut terms {#section-single-cut-decoupling}

<a id="tag-ZYSL" data-assertion="theorem" data-title="Critical single-cut terms factor with the required error for all cluster powers"></a>
<p>Assume <a href="/tag/7GBI/">7GBI</a>. Fix integers $i,j\geq0$, $m\geq1$, and functions $P,Q:\mathbb Z^d\to\mathbb R$ with</p>
<div class="math-display">$$|P(y)|\leq C_P(1+\|y\|^p),\qquad
|Q(z)|\leq C_Q(1+\|z\|^q)$$</div>
<p>for fixed integers $p,q\geq0$. For each $x,y$, use the independent copies of DR5Q:</p>
<div class="math-display">$$A=K_0(\omega_0),\quad C=K_x(\omega_x),\quad
B=K_x(\omega_x|_{A^c}),\quad H=K_y(\omega_y),\quad
\Delta_{S,m}(y)=|H|^m-|K_y(\omega_y|_{S^c})|^m.$$</div>
<p>A cluster with deleted root is empty. For a finite set $S$, put $f_{j,Q}(S)=|S|^j\sum_{z\in S}Q(z)$, setting $f_{j,Q}(\varnothing)=0$ also when $j=0$. Let $W_r=\{x:0&lt;\|x\|\leq r\}$ and define the sums of expectations</p>
<div class="math-display">$$\begin{aligned}
F_{i,m}(P)&=\sum_y P(y)\,\mathbf E_r[|A|^i\Delta_{A,m}(y)],\\
M_j(Q)&=\sum_{x\in W_r}\mathbf E_r f_{j,Q}(B),\\
T_A(P,Q)&=\sum_{x\in W_r}\sum_y P(y)\,\mathbf E_r[|A|^i f_{j,Q}(B)\Delta_{A,m}(y)],\\
T_C(P,Q)&=\sum_{x\in W_r}\sum_y P(y)\,\mathbf E_r[|A|^i f_{j,Q}(B)\Delta_{C,m}(y)].
\end{aligned}$$</div>
<p>Write $m_i=\mathbb E_r|K_0|^i$, with $m_0=1$, and $N=i+j+m$. Then</p>
<div class="math-display">$$\begin{aligned}
T_A(P,Q)&=F_{i,m}(P)M_j(Q)+o\!\left(V_r^N r^{(2N+5)\alpha+p+q}\right),\\
T_C(P,Q)&=m_i\sum_{x\in W_r}\sum_y P(y)\,
\mathbf E_r[f_{j,Q}(C)\Delta_{C,m}(y)]
+o\!\left(V_r^N r^{(2N+5)\alpha+p+q}\right).
\end{aligned}$$</div>
<p>All series of expected absolute values here are finite. The error scale is equivalent, up to a fixed positive factor, to $|W_r|V_r^N r^{p+q}\chi_r^{2N+2}$. The expectations on the second right-hand side use only the independent second and third copies.</p>
<p><em>Proof.</em> We first estimate the cost of replacing $B$ by $C$. Work with nonnegative spatial weights; signed tests follow by absolute values. If $w$ is a nonnegative function and $X=|C|$, the expansion in ordered tuples gives</p>
<div class="math-display">$$\begin{aligned}
0\leq f_{j,w}(C)-f_{j,w}(B)
\leq X^j\sum_{u\in C\setminus B}w(u)
+jX^{j-1}\left(\sum_{z\in C}w(z)\right)|C\setminus B|.
\end{aligned}$$</div>
<p>The second term is omitted when $j=0$. The first term counts loss of the weighted coordinate; the second counts loss of one of the $j$ other coordinates. Likewise</p>
<div class="math-display">$$\Delta_{S,m}(y)\leq m|H|^{m-1}\sum_{a\in H}\mathbf1_{\mathcal D_S(y,a)}.$$</div>
<p>For $u\in C\setminus B$, the original selected geodesic from $x$ to $u$ meets $A$, even if $x\in A$. A cut $\mathcal D_S(y,a)$ forces the original third-copy geodesic from $y$ to $a$ to meet $S$. Use a union bound over these intersection vertices. Independence then separates the factors from the original three configurations. We may enlarge the nonnegative sum over $x\in W_r$ to all $x$.</p>
<p>Keep the notation $R_k,P_{k,s},E_{k,s},C_{k,s}$ of <a href="/tag/PGVH/">PGVH</a>, and put</p>
<div class="math-display">$$Z_{k,s}=P_{k,s}+E_{k,s}+\mathbf1_{\{k\geq1\}}C_{k,s},\qquad
U_{k,s}=\mathbb E_r\left[|K_0|^{k-1}\sum_{z\in K_0}\|z\|^s\right].$$</div>
<p>The last summand in $Z_{0,s}$ is absent. All terms in $Z_{k,s}$ are $o(V_r^k r^{(2k+2)\alpha+s})$.</p>
<p>For the error multiplied by $\Delta_{A,m}$, let $b,c\in A$ be the intersection vertices of the second and third paths. At degree zero the sum of the resulting diagram is exactly</p>
<div class="math-display">$$m_{i+2}R_jR_{m-1},$$</div>
<p>apart from the fixed tuple-counting factor $m(j+1)$. Indeed the two marks in $A$ contribute $m_{i+2}$. For fixed $b$, summing the root $x$, target $u$, and a path through $b$ gives $R_j$ by translation equivariance; the analogous sum through $c$ gives $R_{m-1}$.</p>
<p>For the norm weight $\|y\|^p\|z\|^q$, put $s=p+q$. Since $y=c+(y-c)$ and $z=b+(z-b)$, it suffices to place a degree-$s$ weight on $b$, $c$, $y-c$ or $z-b$. A weight on either mark in $A$ gives $U_{i+2,s}$. Translating a path through its intersection vertex gives $P_{m-1,s}$ for $y-c$. For $z-b$, write $z-b=(z-x)-(b-x)$. If $z$ is the lost coordinate, its first displacement is handled by $E_{j,s}$; if another coordinate is lost, it is handled by $C_{j,s}$, which is needed only when $j\geq1$. The displacement $b-x$ is handled by $P_{j,s}$. Thus the first error is bounded by a constant times</p>
<div class="math-display">$$U_{i+2,s}R_jR_{m-1}
+m_{i+2}Z_{j,s}R_{m-1}
+m_{i+2}R_jP_{m-1,s}.$$</div>
<p>Using PGVH and the moment bounds from AR3F/RM79, every term is $o(V_r^N r^{(2N+5)\alpha+s})$.</p>
<p>For the error multiplied by $\Delta_{C,m}$, the first path still meets $A$ at $b$, while the third path meets $C$ at a mark $c\in C$. At degree zero the diagram sum is now</p>
<div class="math-display">$$m_{i+1}R_{j+1}R_{m-1}.$$</div>
<p>There is one mark in $A$ and an extra unrestricted mark in $C$. For the spatial weight use $y=b+(c-b)+(y-c)$ and $z=b+(z-b)$. Translating the second cluster to $x$, the weights on $c-b$ and $z-b$ are bounded by $Z_{j+1,s}$: a free cluster mark gives $C_{j+1,s}$, a path target gives $E_{j+1,s}$, and the intersection displacement gives $P_{j+1,s}$. The resulting bound is a constant times</p>
<div class="math-display">$$U_{i+1,s}R_{j+1}R_{m-1}
+m_{i+1}Z_{j+1,s}R_{m-1}
+m_{i+1}R_{j+1}P_{m-1,s},$$</div>
<p>again of order $o(V_r^N r^{(2N+5)\alpha+s})$. These estimates include $i=0$, $j=0$, repeated targets and deleted roots. They use only original geodesics and make no assumption about their law after deletion.</p>
<p>Replacing $B$ by $C$ therefore gives both desired factorizations with the unrestricted marginal $M_j^*(Q)=\sum_{x\in W_r}\mathbb E_r f_{j,Q}(C)$ in the first one. This factorization is exact after replacement: $C$ is independent of $(A,\omega_y)$, while $A$ is independent of $(C,\omega_y)$.</p>
<p>To restore the restricted marginal $M_j(Q)$, the same one-path argument, now with one mark in $A$, gives</p>
<div class="math-display">$$|M_j^*(Q)-M_j(Q)|
=o(V_r^j r^{(2j+3)\alpha+q}).$$</div>
<p>For a pure norm weight it is bounded by a constant times $U_{1,q}R_j+\chi_r Z_{j,q}$. Similarly, the single-cut union bound gives</p>
<div class="math-display">$$|F_{i,m}(P)|
=o(V_r^{i+m-1}r^{(2i+2m+1)\alpha+p}),$$</div>
<p>using $U_{i+1,p}R_{m-1}+m_{i+1}P_{m-1,p}$. Their product is $o(V_r^{N-1}r^{(2N+4)\alpha+p+q})$, which is smaller than the required error because $V_rr^\alpha\to\infty$ by <a href="/tag/5J3U/">5J3U</a>. This proves the first formula with $M_j$.</p>
<p>For signed $Q$, the absolute difference of the two cluster functionals is bounded by the same difference with $|Q|$; apply the preceding estimates also with $|P|$. Expanding $(1+\|y\|^p)(1+\|z\|^q)$ reduces the growth bounds to the norm-weight cases already proved. All these bounds concern sums of nonnegative expectations. Tonelli applies before estimating them, and their finiteness justifies the subsequent signed factorizations. For a fixed cutoff the remaining factors with $x\in W_r$ are finite mixed cluster moments, so all displayed series are absolutely convergent.</p>
<p>For $i=j=m=1$, these are the two factorization estimates at the end of the proof of Lemma III.6.11. The result also covers all other cluster powers after JG0C's change of root. Polynomial tests of $y-z$ reduce to these formulas by a finite expansion into products of a function of $y$ and a function of $z$. Redundancy and joint cuts are supplied by 6IJQ and B9Z5. The interception estimate is still needed to replace the joint loss by the sum of the two single losses; consequently ENWJ and RDLW remain conditional.</p>


## Interception repair and remaining assembly {#section-interception-update}

<p><a href="/tag/R6CI/">R6CI</a> now proves the interception estimate of Lemma III.6.17 in prose, closing that particular gap in the preceding discussion. It uses a surviving third-copy path for two BK witnesses and retains the intersection mark on an independent second-copy geodesic. <a href="/tag/IEOH/">IEOH</a> is not used in that reduction. The <a href="/errata/hutchcroft-lrp-3/#interception-diagram-missing-link">provisional source erratum</a> remains, since the printed unrestricted diagram still diverges.</p>
<p>This resolves the interception term for the source's displayed cluster powers. The complete assembly of the triple-interaction expansion, including any additional target-tuple powers required for the deficit equations, must still be checked explicitly. The single-cut factorization ZYSL is already proved above; its existence is distinct from a completed derivation of those equations. ENWJ and RDLW retain their stated deficit-equation hypotheses. No compiled correspondence or author confirmation is inferred from the prose repair.</p>


## The finite Reimer premise {#section-finite-reimer-proof-link}

<p>The <a href="/articles/countable-reimer/#section-finite-reimer-proof">complete finite Reimer proof</a> now supplies the combinatorial premise used in L3TC at the level of the written argument. Its <a href="/articles/countable-reimer/#section-full-reimer-completed-proof">countable extension</a> permits infinite certificates, with the stated distinction between outer and ordinary probability. The hypotheses and tagged statements above are retained; source corrections remain provisional and formal status still requires Lean evidence.</p>
