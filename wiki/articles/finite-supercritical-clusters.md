---
{
  "id": "finite-supercritical-clusters",
  "title": "Large-cluster volume above the finite critical window",
  "subtitle": "Shared boundaries, field growth and concentration",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "The covariance of two small clusters is controlled by the edges joining their boundaries. Combined with field growth, this gives concentration of large-cluster volume and a relative upper bound for the largest component.",
  "context": [
    "The boundary estimate allows arbitrary independent bond probabilities on a finite simple graph.",
    "The critical-reference consequences assume a connected vertex-transitive graph with degree $m$ and $N$ vertices.",
    "All displacements are normalized as $\\varepsilon=m(p-p_c)$."
  ],
  "related": [
    "finite-triangle-window",
    "finite-window-susceptibility",
    "cluster-partitions",
    "ghost-fields"
  ],
  "sourceIds": [
    "borgs-chayes-finite-window"
  ],
  "aliases": [
    "supercritical truncated variance",
    "large-cluster density",
    "finite percolation probability",
    "shared cluster boundaries"
  ],
  "prototypeUses": []
}
---

## A first bound on the largest component {#section-maximum}

<p>On a finite connected simple vertex-transitive graph of degree $m$, write $N=|V|$, $T_p(x,y)=\mathbb P_p(x\leftrightarrow y)$ and $H=\chi(p_c)$. For the critical-reference results below assume</p>
<div class="math-display">$$0<p_c\le\frac12,\qquad H\ge100,\qquad T_{p_c}^3(x,y)\le\mathbf1_{\{x=y\}}+a,\qquad a\le\frac1{100}.$$</div>
<p>Let $L_1$ be the largest component size and, for every real $s>0$, put</p>
<div class="math-display">$$Z_s=\sum_x\mathbf1_{\{|C_x|\ge s\}},\qquad \theta_s=\mathbb P_p(|C_o|\ge s).$$</div>
<p>The cutoff is real: $|C_x|\ge s$ means $|C_x|\ge\lceil s\rceil$. We will first bound $L_1$ on its natural upper scale, then control the fluctuations of $Z_s$ around $N\theta_s$.</p>

<a id="tag-4OVE" data-assertion="theorem" data-title="A first-moment upper bound for the largest component above a finite triangle reference point"></a>
<p>For $p_c\le p\le1/2$, with $\varepsilon=m(p-p_c)\ge0$,</p>
<div class="math-display">$$\mathbb E_pL_1\le22N^{2/3}+192\varepsilon N,\qquad \mathbb P_p\!\left(L_1>A(N^{2/3}+\varepsilon N)\right)\le\frac{192}{A}\quad(A>0).$$</div>
<p><em>Proof.</em> For every integer $k\ge1$, $L_1\le k+Z_k$: if $L_1\ge k$ its vertices are counted by $Z_k$, and otherwise $L_1<k$. Take $k=\lceil N^{2/3}\rceil$ and use the root-tail estimate <a href="/tag/1T2M/">1T2M</a>:</p>
<div class="math-display">$$\mathbb E_pL_1\le k+N\left(20k^{-1/2}+192\varepsilon\right)\le22N^{2/3}+192\varepsilon N.$$</div>
<p>Here $k\le2N^{2/3}$ and $k^{-1/2}\le N^{-1/3}$. Markov's inequality gives the probability bound.</p>

## Shared boundaries and truncated variance {#section-boundaries}

<p>For this section the graph need only be finite, nonempty and simple. Its edges have arbitrary independent opening probabilities $p_e\in[0,1]$. Define</p>
<div class="math-display">$$\chi_{<s}(x)=\mathbb E[|C_x|\mathbf1_{\{|C_x|<s\}}],\qquad D=\max_x\sum_{e\ni x}p_e.$$</div>

<a id="tag-RD1J" data-assertion="theorem" data-title="A shared-boundary variance bound for nonuniform finite percolation"></a>
<p>For every real $s>0$,</p>
<div class="math-display">$$\operatorname{Var}Z_s\le\sum_x\chi_{<s}(x)+\sum_{(u,v):\,u\sim v}p_{\{u,v\}}\,\mathbb E\!\left[|C_u||C_v|\mathbf1_{\{|C_u|<s,\ |C_v|<s,\ C_u\ne C_v\}}\right]\le(1+Ds)\sum_x\chi_{<s}(x).$$</div>
<p>The edge sum is oriented. In particular, for constant probability $p$ on a transitive degree-$m$ graph,</p>
<div class="math-display">$$\operatorname{Var}_pZ_s\le(1+mps)N\chi_{<s}(p).$$</div>
<p><em>Proof.</em> Since $Z_s=N-Z_{<s}$, expand the variance of $Z_{<s}=\sum_x\mathbf1_{\{|C_x|<s\}}$ according to the exact cluster sets $A=C_x$ and $B=C_y$. If $A$ and $B$ intersect, they must be equal for the joint event to occur. Discarding the negative product terms, all intersecting pairs contribute at most</p>
<div class="math-display">$$\sum_A|A|^2\mathbf1_{\{|A|<s\}}\mathbb P(A\text{ is an open component})=\sum_x\chi_{<s}(x).$$</div>
<p>For disjoint $A,B$, let $E(A,B)$ be the edges joining them. The events that $A$ and $B$ are internally connected depend on disjoint edge sets. In the product of their separate cluster probabilities each edge of $E(A,B)$ is required closed twice, whereas in their joint probability it is required closed once. Consequently</p>
<div class="math-display">$$\mathbb P(C_x=A)\mathbb P(C_y=B)=\mathbb P(C_x=A,C_y=B)\prod_{e\in E(A,B)}(1-p_e).$$</div>
<p>This identity uses no division and remains valid when a bond probability is zero or one. Thus the corresponding covariance term is the joint probability multiplied by $1-\prod_{e\in E(A,B)}(1-p_e)$, which is at most $\sum_{e\in E(A,B)}p_e$. Summing first over the root choices $x\in A,y\in B$ gives the oriented-edge term in the statement. For its last bound use $|C_v|<s$, discard the other conditions involving $v$, and sum the incident probabilities at $u$. If $s\le1$, every truncated susceptibility and the variance are zero.</p>

## From a cutoff to a marking field {#section-truncation}

<p>Write $M_x(\gamma)=\mathbb E[1-(1-\gamma)^{|C_x|}]$ for independent vertex marks of probability $\gamma$.</p>
<a id="tag-E4NT" data-assertion="proposition" data-title="A field bound for truncated susceptibility including the singleton cutoff"></a>
<p>On any finite graph with independent bond probabilities, for $s\ge1$,</p>
<div class="math-display">$$\chi_{<s}(x)\le\frac{s}{1-e^{-1}}M_x(1/s)\le2sM_x(1/s).$$</div>
<p>For $1<s\le2$, the exact value is</p>
<div class="math-display">$$\chi_{<s}(x)=\mathbb P(|C_x|=1)=\prod_{e\ni x}(1-p_e).$$</div>
<p><em>Proof.</em> If $1\le k<s$, then</p>
<div class="math-display">$$1-(1-1/s)^k\ge1-e^{-k/s}\ge(1-e^{-1})\frac{k}{s}.$$</div>
<p>The second inequality is concavity of $1-e^{-t}$ on $[0,1]$. Multiply by the probability that $|C_x|=k$ and sum. At $s=1$ the left side is zero. For $1<s\le2$ the only contributing size is one, and the root is isolated precisely when every incident edge is closed.</p>
<p>The last observation repairs a <a href="/errata/borgs-chayes-finite-window/#singleton-truncated-mean">provisional local error</a> in the checked preprint's discussion of $1<s<2$: the truncated mean is at most one, rather than identically one. Its variance theorem is unaffected.</p>

## Growth across a parameter rectangle {#section-rectangle}

<a id="tag-5SCM" data-assertion="proposition" data-title="A rectangle lower bound from the magnetization differential inequality"></a>
<p>Let $M(p,\gamma)$ be positive, continuously differentiable and nondecreasing in both coordinates on a rectangle $[p_0,p]\times[\gamma_0,\gamma]$, where $0<p_0\le p$ and $0<\gamma_0\le\gamma$. Suppose throughout it that</p>
<div class="math-display">$$M\le\gamma M_\gamma+M^2+pMM_p.$$</div>
<p>For every $0<b<1$, writing $M_0=M(p_0,\gamma_0)$,</p>
<div class="math-display">$$M(p,\gamma)\ge\min\left\{\left(\frac\gamma{\gamma_0}\right)^bM_0,\ \frac{p_0}{p}M_0+(1-b)\frac{p-p_0}{p}\right\}.$$</div>
<p><em>Proof.</em> If either side of the rectangle has length zero, monotonicity gives the result. Otherwise divide the differential inequality by $\gamma M$ to obtain</p>
<div class="math-display">$$0\le\partial_\gamma\log M+\frac1\gamma\partial_p(pM-p).$$</div>
<p>Integrate over the rectangle. With $U=M(p,\gamma)$, monotonicity bounds the resulting two integrals above by</p>
<div class="math-display">$$0\le(p-p_0)\log(U/M_0)+\log(\gamma/\gamma_0)\{pU-p_0M_0-(p-p_0)\}.$$</div>
<p>If $U\ge(\gamma/\gamma_0)^bM_0$, the first alternative holds. Otherwise divide by the positive logarithm and use $\log(U/M_0)<b\log(\gamma/\gamma_0)$; this gives $pU\ge p_0M_0+(1-b)(p-p_0)$, the second alternative.</p>
<p>Finite transitive percolation satisfies this differential inequality by the finite Aizenman–Barsky argument used in <a href="/tag/KQN9/">KQN9</a>. At positive field its magnetization is positive and polynomial, so the rectangle argument applies without a limiting or differentiability assumption.</p>

## The density of vertices in large clusters {#section-density}

<p>Return to the critical-reference hypotheses and put $H=\lambda N^{1/3}$ with $\lambda>0$. Fix $0<\alpha<1$. For $p=p_c+\varepsilon/m\le1/2$, $0<\varepsilon\le1$, define</p>
<div class="math-display">$$R=\varepsilon N^{1/3},\qquad s=\varepsilon^{-2}R^\alpha,\qquad\theta_s=\mathbb P_p(|C_o|\ge s).$$</div>

<a id="tag-UQ45" data-assertion="theorem" data-title="A density of order epsilon above the mesoscopic finite-graph cutoff"></a>
<p>There are positive constants $c=c(\alpha,\lambda)$ and $R_0=R_0(\alpha,\lambda)$ such that, whenever $R\ge R_0$,</p>
<div class="math-display">$$c\varepsilon\le\theta_s\le212\varepsilon.$$</div>
<p>The following explicit choices suffice:</p>
<div class="math-display">$$b=\frac1{2-\alpha},\quad\zeta=\min\left\{\frac12,\frac{1-b}{2000},\left(\frac{\lambda^{\alpha b}}{2000}\right)^{1/(1-b)}\right\},$$</div>
<div class="math-display">$$c=\frac16\min\{1-b,\zeta^b\lambda^{\alpha b}\},\qquad R_0=\max\{1,(\zeta\lambda^2)^{-b}\}.$$</div>
<p><em>Proof.</em> For any real $s\ge1$, the field estimate in the proof of <a href="/tag/1T2M/">1T2M</a> gives</p>
<div class="math-display">$$M(p,1/s)\le10s^{-1/2}+96\varepsilon.$$</div>
<p>For $s\ge2$ this follows from $M\le\sqrt{96/s}+96\varepsilon$; for $1\le s<2$ use $M\le1$. Since $R\ge1$, our cutoff satisfies $s\ge\varepsilon^{-2}\ge1$, so $M(p,1/s)\le106\varepsilon$. A cluster of size at least $s$ contains a mark of probability $1/s$ with probability at least $1-e^{-1}$. Thus $\theta_s\le2M(p,1/s)\le212\varepsilon$.</p>
<p>For the lower bound apply the rectangle lemma from $(p_c,\gamma_0)$ to $(p,\gamma)$, where $\gamma_0=H^{-2}$ and $\gamma=\zeta/s$. The choice of $R_0$ ensures</p>
<div class="math-display">$$\frac\gamma{\gamma_0}=\zeta\lambda^2R^{2-\alpha}\ge1.$$</div>
<p>Both fields lie strictly between zero and one. The critical field lower bound <a href="/tag/KQN9/">KQN9</a> gives $M(p_c,\gamma_0)\ge1/(3H)$, while <a href="/tag/F5Y5/">F5Y5</a> gives $mp_c\le100/99$, so $(p-p_c)/p=\varepsilon/(mp_c+\varepsilon)\ge\varepsilon/3$. Consequently the two alternatives in the rectangle bound yield</p>
<div class="math-display">$$M(p,\zeta/s)\ge\frac\varepsilon3\min\{\zeta^b\lambda^{\alpha b},1-b\}.$$</div>
<p>Here $(2-\alpha)b=1$ and $2b-1=\alpha b$. To turn this field estimate into a tail, split its expectation at $|C_o|<s$. For every integer $k<s$, the inequalities $1-(1-\zeta/s)^k\le\zeta k/s$ and $k/s\le e[1-(1-1/s)^k]$ give</p>
<div class="math-display">$$\theta_s\ge M(p,\zeta/s)-e\zeta M(p,1/s).$$</div>
<p>By the choice of $\zeta$, both $2000\zeta\le1-b$ and $2000\zeta\le\zeta^b\lambda^{\alpha b}$. Since $106e<2000/6$, the subtracted term is at most $\varepsilon\min\{1-b,\zeta^b\lambda^{\alpha b}\}/6$. This proves the lower bound. The cutoff is kept real throughout; no rounding error enters either field comparison.</p>

## Concentration and the relative upper bound {#section-concentration}

<a id="tag-G987" data-assertion="theorem" data-title="Concentration of supercritical large-cluster volume and a relative largest-component upper bound"></a>
<p>With the same hypotheses, let</p>
<div class="math-display">$$\eta=\frac{3-2\alpha}{15-6\alpha},\qquad u=\varepsilon N^\eta.$$</div>
<p>If $R\ge1$, then for every $t>0$,</p>
<div class="math-display">$$\operatorname{Var}_pZ_s\le848\varepsilon Ns^2,\qquad \mathbb P_p(|Z_s-N\theta_s|\ge t\varepsilon N)\le\frac{848}{t^2u^{5-2\alpha}}.$$</div>
<p>If moreover $R\ge R_*:=\max\{R_0,c^{-1/(3-\alpha)}\}$, where $c,R_0$ are as above, then</p>
<div class="math-display">$$\mathbb P_p\!\left(L_1\le(1+u^{-1})N\theta_s\right)\ge1-\frac{848}{c^2u^{3-2\alpha}}.$$</div>
<p><em>Proof.</em> We have $mp=mp_c+\varepsilon<3$. The shared-boundary bound, the field bound for the truncated susceptibility and $M(p,1/s)\le106\varepsilon$ imply</p>
<div class="math-display">$$\operatorname{Var}Z_s\le(1+mps)N\chi_{<s}\le4sN\cdot2sM(p,1/s)\le848\varepsilon Ns^2.$$</div>
<p>Chebyshev gives $848s^2/(t^2\varepsilon N)$. The identities</p>
<div class="math-display">$$\frac{s^2}{\varepsilon N}=\frac1{\varepsilon^{5-2\alpha}N^{1-2\alpha/3}}=u^{-(5-2\alpha)},\qquad \eta(5-2\alpha)=1-\frac{2\alpha}{3}$$</div>
<p>prove the concentration estimate. For the last assertion, $N\theta_s\ge c\varepsilon N\ge s$ because $\varepsilon N/s=R^{3-\alpha}$ and $R\ge R_*$. If $L_1>(1+u^{-1})N\theta_s$, its component is counted by $Z_s$, and therefore</p>
<div class="math-display">$$Z_s-N\theta_s>u^{-1}N\theta_s\ge c\varepsilon N/u.$$</div>
<p>Apply the concentration estimate with $t=c/u$.</p>
<p>For a sequence with fixed $\alpha,\lambda$ and $u\to\infty$, these estimates give $Z_s/(N\theta_s)\to1$ in probability and $L_1\le(1+o(1))N\theta_s$ with probability tending to one. They do not assert that the large-cluster volume belongs to one component. A matching lower bound for $L_1$, or uniqueness of a giant component, requires an additional argument. The scale $\varepsilon N^\eta\to\infty$ is also stronger than merely being above the window, $\varepsilon N^{1/3}\to\infty$.</p>


## The supercritical complete-graph exploration {#section-er-exploration}

<p>We now specialize to $G(N,p)$ with $p=(1+\varepsilon)/N$, where $\varepsilon\to0$ and $R=N\varepsilon^3\to\infty$. Here $\varepsilon$ is defined by this complete-graph parametrization. The earlier finite-triangle assumptions are not needed.</p>
<p>Process vertices one at a time. If the active queue is empty, choose the least undiscovered vertex as a new root; otherwise take the first active vertex. Reveal its bonds to all still undiscovered vertices and add its new neighbours to the queue. Let $A_t$ be the number of active vertices after $t$ vertices have been processed, starting with $A_0=0$. Write $\eta_t$ for the number newly discovered at step $t$, and set</p>
<div class="math-display">$$Y_t=\sum_{i=1}^t(\eta_i-1),\qquad
C_t=\sum_{i=1}^t\mathbf1_{\{A_{i-1}=0\}},\qquad Y_0=C_0=0.$$</div>
<p>Thus $C_t$ counts component starts and $A_t=Y_t+C_t$. With $\mathcal F_t$ denoting the full exploration history, the tests at the next step are fresh, so</p>
<div class="math-display">$$\eta_t\mid\mathcal F_{t-1}\ \sim
\operatorname{Bin}\!\left(N-t+1-A_{t-1}-\mathbf1_{\{A_{t-1}=0\}},p\right).$$</div>
<p>The last subtraction removes a newly selected root from the undiscovered vertices before testing its bonds. The queue recursion also gives, for $t\ge1$,</p>
<div class="math-display">$$C_t=1-\min_{0\le s<t}Y_s,\qquad
A_t=Y_t+1-\min_{0\le s<t}Y_s.$$</div>
<p>Indeed the increments of $Y$ are at least $-1$, and each component ends when $Y$ first drops one unit below its value before that component began. In particular, $A_t=0$ exactly at strict descending record times of $Y$. Consecutive such times differ by a component size.</p>

<a id="tag-AUTD" data-assertion="theorem" data-title="The barely supercritical complete-graph exploration follows a parabola uniformly on the epsilon N time scale"></a>
<p>For every fixed $a>0$, put $T=\lfloor a\varepsilon N\rfloor$. There is a constant $K_a<\infty$ such that, for all sufficiently large $N$,</p>
<div class="math-display">$$\mathbb E\max_{0\le t\le T}
\left|\frac{Y_t}{\varepsilon^2N}
-\left(\frac{t}{\varepsilon N}-\frac12\left(\frac{t}{\varepsilon N}\right)^2\right)\right|^2
\le K_a\left(\frac1R+\varepsilon^2+\frac1{(\varepsilon N)^2}\right).$$</div>
<p>In particular the scaled exploration converges uniformly in probability to $s-s^2/2$ on each fixed bounded time interval.</p>
<p><em>Proof.</em> Let</p>
<div class="math-display">$$M_t=\sum_{i=1}^t\bigl(\eta_i-\mathbb E[\eta_i\mid\mathcal F_{i-1}]\bigr),
\qquad W_T=\max_{0\le t\le T}|M_t|.$$</div>
<p>Each conditional offspring variance is at most $Np=1+\varepsilon$, so orthogonality of martingale increments and Doob's inequality give</p>
<div class="math-display">$$\mathbb EW_T^2\le4(1+\varepsilon)T.$$</div>
<p>Also $\mathbb E[\eta_i-1\mid\mathcal F_{i-1}]\le\varepsilon$. Within a component that starts just after time $s$, the queue is $1+Y_t-Y_s$ until it empties. Thus, including times when the queue is empty,</p>
<div class="math-display">$$A_t\le1+\varepsilon t+2W_T\qquad(0\le t\le T).$$</div>
<p>Summing the exact conditional means now gives</p>
<div class="math-display">$$Y_t=M_t+\varepsilon t-\frac p2t(t-1)
-p\sum_{i=1}^t A_{i-1}-pC_t.$$</div>
<p>Use the queue bound and $C_t\le t$. For $0<\varepsilon<1$, $p\le2/N$, and $t\le T\le a\varepsilon N$, this yields</p>
<div class="math-display">$$\max_{t\le T}\left|Y_t-\varepsilon t+\frac{t^2}{2N}\right|
\le(1+4a\varepsilon)W_T+5a\varepsilon+\frac52a^2\varepsilon^3N.$$</div>
<p>For example, the difference between the two quadratic drift terms is at most $pT/2+\varepsilon T^2/(2N)$; the queue and restart sums contribute at most $pT(1+\varepsilon T+2W_T)+pT$. Squaring, taking expectations and dividing by $\varepsilon^4N^2$ proves the bound. All its right-hand terms vanish in the stated regime. Replacing $t/(\varepsilon N)$ by a real time and taking its integer part adds a uniform error of order $(\varepsilon N)^{-1}$.</p>

## One giant and the remaining component sizes {#section-er-giant}

<p>Order all component sizes as $L_1\ge L_2\ge\cdots$, with zeros appended if necessary, and keep $\varepsilon\to0$ and $N\varepsilon^3\to\infty$.</p>

<a id="tag-2KT9" data-assertion="theorem" data-title="Barely supercritical complete graphs have one giant of size two epsilon N and logarithmic fixed-rank remaining components"></a>
<p>In probability,</p>
<div class="math-display">$$\frac{L_1}{2\varepsilon N}\longrightarrow1,
\qquad
\frac{L_r}{2\varepsilon^{-2}\log(N\varepsilon^3)}\longrightarrow1
\quad\text{for every fixed integer }r\ge2.$$</div>
<p>In particular $L_2/(\varepsilon N)\to0$: only one component has size of order $\varepsilon N$.</p>
<p><em>Proof.</em> Fix $0<\delta<1/4$ and take integer times near $\delta\varepsilon N$, $(2-\delta)\varepsilon N$ and $(2+\delta)\varepsilon N$, denoted by $t_-$, $t_+$ and $t_*$. Use the floor for $t_-$ and ceilings for the other two. AUTD with $a=3$ implies, with probability tending to one, that $Y_t>0$ for all $t_-\le t\le t_+$ and</p>
<div class="math-display">$$Y_{t_*}<\min_{0\le t\le t_-}Y_t-1.$$</div>
<p>To obtain the second inequality, the limiting parabola is nonnegative before time $\delta$ and strictly negative at $2+\delta$; also $\varepsilon^2N\to\infty$. The first inequality means that one component is being processed throughout the middle interval. Its start time $\tau$ is before $t_-$, and its completion time $\sigma$ is after $t_+$. The record-time identity forces $\sigma\le t_*$, since otherwise the last displayed inequality would take the still active queue below zero. This component therefore has size between $(2-2\delta)\varepsilon N-O(1)$ and $(2+\delta)\varepsilon N+O(1)$. All components processed before it have total size at most $t_-$.</p>
<p>Define $\sigma$ on every outcome as the first time at or after $t_+$ at which $A_\sigma=0$. It is a stopping time, and it is the completion time just described on the event above. Conditional on $\mathcal F_\sigma$, the $M=N-\sigma$ undiscovered vertices induce an independent $G(M,p)$: no edge with both endpoints undiscovered has been tested. This assertion conditions only on the stopped history, not on the event that the whole exploration stays close to its parabola.</p>
<p>Uniformly when $t_+\le\sigma\le t_*$, put $\varepsilon'=1-Mp$. For large $N$,</p>
<div class="math-display">$$M\ge N/2,\qquad \varepsilon'\ge\varepsilon/2,
\qquad \varepsilon'=O(\varepsilon),\qquad
I'=-\varepsilon'-\log(1-\varepsilon')\ge\varepsilon^2/8.$$</div>
<p>The <a href="/tag/RN5K/">subcritical complete-graph bound</a>, applied conditionally with $k=\lceil\delta\varepsilon N\rceil$, gives</p>
<div class="math-display">$$\mathbb P\!\left(L_1(G(M,p))\ge k\mid\mathcal F_\sigma\right)
\le C_\delta R^{-3/2}e^{-\delta R/8}=o(1)$$</div>
<p>on this range of $\sigma$. Here $1-e^{-I'}\ge I'/2$ eventually and the polynomial prefactor is bounded by a constant times $N\varepsilon^{-2}(\varepsilon N)^{-5/2}=R^{-3/2}$. Integrating this uniform conditional estimate controls the remainder on the high-probability exploration event. All other components, before or after the long excursion, consequently have size at most $\delta\varepsilon N+O(1)$ with probability tending to one. Letting $\delta\downarrow0$ proves $L_1/(\varepsilon N)\to2$ and $L_2/(\varepsilon N)\to0$.</p>
<p>To refine the latter scale, let $a_\delta=(2-\delta)\varepsilon N$, $b_\delta=(2+\delta)\varepsilon N$, and let $E_\delta$ be the event that one component has size in $[a_\delta,b_\delta]$ and all others have size less than $a_\delta$. The limits just proved imply $\mathbb P(E_\delta)\to1$. Conditional on $E_\delta$ and on the vertex set $S$ of that component, the graph on its $m=N-|S|$ remaining vertices has law</p>
<div class="math-display">$$G(m,p)\ \text{conditioned on}\ \{L_1(G(m,p))<a_\delta\}.$$</div>
<p>This follows directly from independence: the event specifying $S$ requires its internal connectivity and its closed boundary, while the only condition involving edges in its complement is the displayed size bound. Thus deleting a selected giant does impose a condition on the remainder.</p>
<p>For all these $m$, write $d_m=1-mp$. Uniformly over the possible sizes of $S$,</p>
<div class="math-display">$$1-\delta+o(1)\le\frac{d_m}{\varepsilon}\le1+\delta+o(1),
\qquad m/N\to1.$$</div>
<p>The same subcritical tail bound shows that the conditioning event has probability $1-o(1)$ uniformly in $m$. Conditioning therefore changes probabilities by $o(1)$ uniformly. The <a href="/tag/X0R0/">subcritical fixed-rank law</a> applies to $G(m,(1-d_m)/m)$, since $d_m\to0$ and $md_m^3\to\infty$ uniformly. Its probability convergence is uniform over these parameters: a sequence of violating choices of $m$ would contradict that law. For each fixed rank $j$, its scale is</p>
<div class="math-display">$$b_m=2d_m^{-2}\log(md_m^3),\qquad
\frac{b_m}{2\varepsilon^{-2}\log R}
=\left(\frac{\varepsilon}{d_m}\right)^2(1+o(1)).$$</div>
<p>On $E_\delta$, $L_{j+1}$ is exactly the $j$th largest size in this complement. Mix the uniform estimates over $S$, then let $\delta\downarrow0$. This gives the asserted logarithmic law for every fixed rank after the giant.</p>

## Mean size of the giant {#section-er-giant-mean}

<a id="tag-U6EN" data-assertion="theorem" data-title="The barely supercritical complete-graph giant has its leading size in mean absolute error and all other components have negligible mean on that scale"></a>
<p>Under the same assumptions,</p>
<div class="math-display">$$\mathbb E\left|\frac{L_1}{2\varepsilon N}-1\right|\longrightarrow0,
\qquad \frac{\mathbb EL_2}{\varepsilon N}\longrightarrow0.$$</div>
<p>In particular $\mathbb EL_1\sim2\varepsilon N$, and the second conclusion holds with any fixed $r\ge2$ in place of $2$.</p>
<p><em>Proof.</em> To control the expectation, dominate a root exploration by independent rows of $N$ Bernoulli-$p$ variables, and then by Poisson offspring with mean</p>
<div class="math-display">$$\mu=N[-\log(1-p)]
=1+\varepsilon+O(N^{-1}).$$</div>
<p>The Poisson coupling realizes each Bernoulli variable as the positive indicator of a Poisson variable of mean $-\log(1-p)$. Since $N\varepsilon\to\infty$, we have $\mu-1\sim\varepsilon$. Let $\rho$ be the survival probability of this Poisson branching process. The <a href="/tag/BFM4/">extinction criterion</a> and generating-function equation give $\rho>0$ and</p>
<div class="math-display">$$1-\rho=e^{-\mu\rho},\qquad
\mu=\frac{-\log(1-\rho)}\rho
=1+\frac\rho2+O(\rho^2).$$</div>
<p>Here $\rho\to0$: any positive subsequential limit would make the middle expression strictly greater than one, contradicting $\mu\to1$; a limit of one is also excluded by that expression. Thus $\rho\sim2\varepsilon$.</p>
<p>For the finite progeny, <a href="/tag/RL1L/">Dwass's formula</a> and Stirling give</p>
<div class="math-display">$$\mathbb P(T=j)
=\frac{e^{-\mu j}(\mu j)^{j-1}}{j!}
\le\frac{j^{-3/2}}{\mu\sqrt{2\pi}}
e^{-j(\mu-1-\log\mu)}\le Cj^{-3/2}.$$</div>
<p>Since the mass at $T=\infty$ is $\rho$, for every $k\ge1$ the root bound is $\mathbb P(|C(v)|\ge k)\le\rho+Ck^{-1/2}$. Take $k=\lceil\varepsilon^{-2}R^{1/2}\rceil$. If $Z_k$ counts vertices in components of size at least $k$, then $L_1\le k+Z_k$, and hence</p>
<div class="math-display">$$\mathbb EL_1\le k+N\rho+CNk^{-1/2}=(2+o(1))\varepsilon N.$$</div>
<p>Indeed $k/(\varepsilon N)=O(R^{-1/2})$ and $(\varepsilon\sqrt k)^{-1}=O(R^{-1/4})$. The probability limit in 2KT9 supplies the matching lower limit for the normalized expectation. With $X=L_1/(\varepsilon N)$, we therefore have $X\to2$ in probability and $\mathbb EX\to2$. The bounded variables $(2-X)_+$ have expectations tending to zero, so</p>
<div class="math-display">$$\mathbb E|X-2|=\mathbb EX-2+2\mathbb E(2-X)_+\longrightarrow0.$$</div>
<p>Finally $Z=L_2/(\varepsilon N)\to0$ in probability and $0\le Z\le X$. The inequality $Z\le|X-2|+\min\{Z,2\}$ proves $\mathbb EZ\to0$.</p>
<p>This completes the leading giant-size statement in mean as well as probability, and the probability law for the remaining fixed ranks on their smaller logarithmic scale. It does not give convergence of their means on that smaller scale, a centered giant fluctuation law, or a giant-component lower bound for general finite transitive graphs.</p>


## Short paths supplied by expansion {#section-expander-paths}

<p>A geometric hypothesis can turn large-cluster mass into one giant. In this section $G=(V,E)$ is a finite simple graph with $N\ge1$ vertices, maximum degree at most $d$, and a constant $h>0$ such that</p>
<div class="math-display">$$|\partial_E S|\ge h\min\{|S|,N-|S|\}\qquad(S\subseteq V),$$</div>
<p>where $\partial_E S$ consists of the edges with exactly one endpoint in $S$. No transitivity or triangle condition is assumed.</p>

<a id="tag-9906" data-assertion="proposition" data-title="Edge expansion supplies linearly many short edge-disjoint paths between two macroscopic vertex sets"></a>
<p>Let $0<\delta\le1/2$ and let $A,B\subseteq V$ be disjoint sets with $|A|,|B|\ge\delta N$. Put</p>
<div class="math-display">$$\ell=\left\lceil\frac d{h\delta}\right\rceil,
\qquad \kappa=\frac{h\delta}{2}q^\ell\quad(0<q\le1).$$</div>
<p>There are at least $h\delta N/2$ pairwise edge-disjoint $A$–$B$ paths of length at most $\ell$. Consequently, independent bond percolation with parameter $q$ satisfies</p>
<div class="math-display">$$\mathbb P_q(A\not\leftrightarrow B)\le e^{-\kappa N}.$$</div>
<p><em>Proof.</em> Every cut separating $A$ from $B$ is the boundary of a set $S$ with $A\subseteq S\subseteq V\setminus B$. Both $S$ and its complement have at least $\delta N$ vertices, so its size is at least $h\delta N$. The finite edge form of Menger's theorem therefore gives at least $h\delta N$ edge-disjoint paths. One way to see the needed form is to give each edge unit capacity, connect a source to $A$ and $B$ to a sink with capacities larger than $|E|$, and augment integral flows. When no augmenting path remains, the reachable set gives a cut equal to the flow value. Cancel opposite flows on an undirected edge and decompose the remaining integral flow into paths.</p>
<p>Choose these paths simple. Their total length is at most $|E|\le dN/2$. Fewer than $dN/(2\ell)\le h\delta N/2$ of them have length greater than $\ell$, leaving the asserted number of short paths. Each short path is entirely open with probability at least $q^\ell$, and these events are independent because the paths share no edges. Their simultaneous failure has probability at most $(1-q^\ell)^{h\delta N/2}\le e^{-\kappa N}$.</p>

## Sprinkling joins the large clusters {#section-expander-sprinkling}

<a id="tag-NVCH" data-assertion="proposition" data-title="Independent sprinkling joins all but a prescribed small fraction of the large-cluster mass on a bounded-degree expander"></a>
<p>Fix any initial bond configuration $\omega$ on $G$, an integer $M\ge1$, and let $U$ be the union of its components of size at least $M$. Write $W=|U|$. Add independent Bernoulli-$q$ bonds $\eta$ and let</p>
<div class="math-display">$$H=\max\{|C\cap U|:C\text{ is a component of }\omega\cup\eta\}.$$</div>
<p>For $\delta,\ell,\kappa$ as in 9906, whenever $W\ge3\delta N$,</p>
<div class="math-display">$$\mathbb P(H\le W-\delta N\mid\omega)
\le\min\left\{1,\exp\left[N\left(\frac{\log2}{M}-\kappa\right)\right]\right\}.$$</div>
<p>In particular, if $M\ge2\log2/\kappa$, this probability is at most $e^{-\kappa N/2}$. The bound holds uniformly in the initial configuration, so it also holds after conditioning on an independently sampled first round.</p>
<p><em>Proof.</em> There are at most $N/M$ initial components contributing to $U$. A partition of this family into two parts determines disjoint vertex unions $A,B$ with $A\cup B=U$. For each partition with $|A|,|B|\ge\delta N$, 9906 bounds the probability that the sprinkled bonds contain no $A$–$B$ path by $e^{-\kappa N}$. There are at most $2^{N/M}$ partitions. Hence, except on an event of the stated probability, every such partition is joined by a sprinkled path. These paths may run through vertices outside $U$; that only helps connect the initial components.</p>
<p>To conclude, give each final component weight $|C\cap U|$. Each initial component lies wholly in one final component, and the weights sum to $W$. If a weight is at least $\delta N$ but at most $W-\delta N$, it and the remaining weights give a partition forbidden by the preceding event. If all weights are smaller than $\delta N$, collect them until their sum first reaches $\delta N$. The sum is less than $2\delta N$, and the remaining sum is greater than $\delta N$ because $W\ge3\delta N$. This again gives a forbidden partition. Thus some weight is greater than $W-\delta N$.</p>

## The giant density on locally tree-like expanders {#section-expander-density}

<p>Let $(G_n)$ be finite simple $d$-regular graphs, for a fixed integer $d\ge3$, with $N_n=|V(G_n)|\to\infty$. Suppose the edge-expansion inequality above holds with the same $h>0$ for every $n$. Assume also that, for every fixed radius $R$, the fraction of vertices whose rooted radius-$R$ neighbourhood is isomorphic to that in the infinite $d$-regular tree tends to one. Girth tending to infinity is a sufficient, stronger condition.</p>
<p>Let $L_1\ge L_2\ge\cdots$ be the percolation component sizes, padded with zeros. For $p\in[0,1]$, define</p>
<div class="math-display">$$u_p=\min\{u\in[0,1]:u=1-p+pu^{d-1}\},
\qquad \rho_d(p)=1-u_p^d.$$</div>
<p>Thus $u_p$ is the probability that a specified branch from the root of the infinite tree does not lead to infinity, including the possibility that its first bond is closed. The root has $d$ independent branches, so $\rho_d(p)$ is its survival probability.</p>

<a id="tag-YTZU" data-assertion="theorem" data-title="The giant density on locally tree-like regular expanders equals the regular-tree survival probability"></a>
<p>For every fixed $p\in[0,1]$, independent bond percolation on $G_n$ satisfies</p>
<div class="math-display">$$\frac{L_1}{N_n}\longrightarrow\rho_d(p),\qquad
\frac{L_2}{N_n}\longrightarrow0$$</div>
<p>in probability and in mean absolute error. In particular the limiting largest-component density is positive exactly when $p>1/(d-1)$.</p>
<p><em>Proof.</em> Write $N=N_n$, and for a fixed integer $M\ge1$ let</p>
<div class="math-display">$$Z_M=\sum_{v\in V(G_n)}\mathbf1_{\{|C(v)|\ge M\}},\qquad
\theta_M(p)=\mathbb P_p^{T_d}(|C(o)|\ge M).$$</div>
<p>The event $|C(v)|\ge M$ is determined by the bonds within the host ball of radius $M-1$ about $v$. Indeed any connected cluster with at least $M$ vertices contains a connected set of exactly $M$ vertices containing $v$, all within this ball. Conversely such an open connected set witnesses the event. Local convergence therefore gives $\mathbb E Z_M/N\to\theta_M(p)$.</p>
<p>The two indicators at $v,w$ are independent when their host balls are disjoint. For fixed $M$, bounded degree gives a constant $D_{d,M}$ bounding the number of vertices within distance $2M$ of any vertex. Bounding the remaining covariances in absolute value by one yields</p>
<div class="math-display">$$\operatorname{Var}(Z_M)\le ND_{d,M},\qquad
\frac{Z_M}{N}\longrightarrow\theta_M(p)\quad\text{in probability}.$$</div>
<p>Since $L_1\le M+Z_M$ and $\theta_M(p)\downarrow\rho_d(p)$ as $M\to\infty$, this proves the required upper bound for $L_1/N$. The <a href="/tag/BFM4/">branching-process extinction criterion</a>, applied to the $\operatorname{Bin}(d-1,p)$ descendants of a nonroot vertex, gives $\rho_d(p)=0$ for $p\le1/(d-1)$ and $\rho_d(p)>0$ above this value. The critical offspring law is nondegenerate. Thus the theorem already follows at and below the critical value, including the second-largest-component statement.</p>
<p>For $p>1/(d-1)$ choose $1/(d-1)<p_1<p$ and put $q=(p-p_1)/(1-p_1)$. The union of independent $p_1$ and $q$ percolations has law $p$. Fix $0<\delta<\rho_d(p_1)/4$, define $\kappa$ using this $\delta$ and $q$, and choose a fixed integer $M\ge2\log2/\kappa$. In the first round,</p>
<div class="math-display">$$\frac WN=\frac{Z_M(p_1)}N\longrightarrow\theta_M(p_1)\ge\rho_d(p_1)>4\delta.$$</div>
<p>With probability tending to one, therefore, $W\ge3\delta N$. Conditional on the entire first round, NVCH supplies a final component containing more than $W-\delta N$ of these vertices, except with probability $e^{-\kappa N/2}$. It follows that, for every $a>0$,</p>
<div class="math-display">$$\mathbb P_p\left(\frac{L_1}{N}<\rho_d(p_1)-\delta-a\right)\longrightarrow0.$$</div>
<p>First let $\delta\downarrow0$, then $p_1\uparrow p$. The tree survival probability is continuous from the left above its critical point, including at $p=1$. To check this directly, the branch-failure probabilities $u_{p_1}$ decrease as $p_1$ increases. Once $p_1$ is bounded above criticality they are bounded away from one. Their limit solves $u=1-p+pu^{d-1}$ and is less than one, so it is the unique subunit root $u_p$. This proves the matching lower bound.</p>
<p>For uniqueness, fix $a>0$ and choose $M$ so that $\theta_M(p)<\rho_d(p)+a/4$. With probability tending to one, $L_1/N>\rho_d(p)-a/4$, $Z_M/N<\rho_d(p)+a/2$, and $L_1\ge M$. If also $L_2\ge aN$, then both largest components are counted in $Z_M$ for large $N$, giving $Z_M/N\ge L_1/N+a>\rho_d(p)+3a/4$, a contradiction. Hence $L_2/N\to0$. Finally $0\le L_i/N\le1$, so both probability limits also hold in mean absolute error.</p>
<p>This is a fixed-parameter theorem for bounded-degree expanding graphs with the stated local limit. It supplies neither a rate as $p$ approaches $1/(d-1)$ nor a logarithmic bound on $L_2$. The high-dimensional torus and near-critical hypercube require different geometric estimates.</p>
<p>The short-path sprinkling method is due to <a href="https://web.math.princeton.edu/~nalon/PDFS/abs8.pdf">Alon–Benjamini–Stacey, Section 3</a>; <a href="https://www.cs.tau.ac.il/~krivelev/expperc.pdf">Krivelevich–Lubetzky–Sudakov, Claim 2.3 and Theorem 1</a> give the high-girth density result and stronger conclusions. The proof here uses fixed cluster-size cutoffs and bounded dependence to allow a vanishing fraction of exceptional local neighbourhoods.</p>


## Concentration of locally weighted cluster mass {#section-expander-local-concentration}

<p>For a finite simple graph with $N\ge1$ vertices and maximum degree at most $d\ge1$, let $B_G(v,R)$ be the induced host ball. Fix integers $M\ge1$ and $R\ge0$. For each vertex choose a function $f_v$ with values in $[0,1]$, determined by the bond states within $B_G(v,R)$, and put</p>
<div class="math-display">$$F_{M,f}=\sum_v f_v\mathbf1_{\{|C(v)|\ge M\}},\qquad
D_{d,R}=\sum_{j=0}^R d^j,\qquad K=2(M-1)+2D_{d,R}.$$</div>
<p>The functions may differ between vertices. The probabilities of the independent bonds may also differ.</p>

<a id="tag-YCHK" data-assertion="proposition" data-title="Locally weighted large-cluster mass has a finite independent-bond concentration bound"></a>
<p>For every $t\ge0$,</p>
<div class="math-display">$$\mathbb P\bigl(|F_{M,f}-\mathbb EF_{M,f}|\ge t\bigr)
\le\min\left\{1,2\exp\left(-\frac{4t^2}{dNK^2}\right)\right\}.$$</div>
<p>For the unweighted mass $Z_M=\sum_v\mathbf1_{\{|C(v)|\ge M\}}$ and $M\ge2$, the sharper bound is</p>
<div class="math-display">$$\mathbb P(|Z_M-\mathbb EZ_M|\ge t)
\le\min\left\{1,2\exp\left(-\frac{t^2}{dN(M-1)^2}\right)\right\}.$$</div>
<p>When $M=1$, $Z_M=N$ deterministically.</p>
<p><em>Proof.</em> Opening one bond either leaves the component partition unchanged or joins two components. A vertex changes its size-cutoff indicator only if it belonged to a component smaller than $M$ before the opening. If both joined components were smaller than $M$, there are at most $2(M-1)$ such vertices; if only one was smaller, there are at most $M-1$. Thus a bond flip changes at most $2(M-1)$ cutoff indicators. It changes $f_v$ only when $B_G(v,R)$ contains that bond. Such a root is within distance $R$ of an endpoint, so there are at most $2D_{d,R}$ of them. Splitting the change in each product into its indicator and function changes shows that $F_{M,f}$ changes by at most $K$. For $Z_M$ the function-change term is absent.</p>
<p>Reveal the $m=|E|$ independent bonds in a fixed order. In the associated Doob martingale, the two possible next conditional expectations differ by at most $K$: couple the unrevealed bonds identically in the two cases and use the preceding bound. The martingale increment is therefore a centered two-point variable whose two values differ by at most $K$. The <a href="/tag/XSA6/">Bernoulli exponential-moment calculation</a>, scaled by that difference and applied conditionally, gives</p>
<div class="math-display">$$\mathbb E e^{\lambda(F_{M,f}-\mathbb EF_{M,f})}
\le e^{mK^2\lambda^2/8}.$$</div>
<p>Exponential Markov and optimization give each one-sided tail at most $\exp[-2t^2/(mK^2)]$ when $m>0$. Use $m\le dN/2$ and add the two tails. If $m=0$ the variable is deterministic. Replacing $K$ by $2(M-1)$ gives the unweighted bound.</p>

## Exponential control at a fixed parameter {#section-expander-exponential}

<a id="tag-UPQ2" data-assertion="theorem" data-title="Fixed-size deviations of the giant density on locally tree-like expanders have exponentially small probability"></a>
<p>Under the graph-sequence hypotheses of YTZU, fix $p\in[0,1]$ and $a>0$. There are constants $c,C>0$ and an index $n_0$ such that, for every $n\ge n_0$,</p>
<div class="math-display">$$\mathbb P_p\left(\left|\frac{L_1}{N_n}-\rho_d(p)\right|\ge a
\ \text{or}\ \frac{L_2}{N_n}\ge a\right)\le Ce^{-cN_n}.$$</div>
<p>The constants $c,C$ can depend on $d,h,p,a$; the index $n_0$ can also depend on the rate of local convergence of the graph sequence.</p>
<p><em>Proof.</em> Write $N=N_n$ and $\rho=\rho_d(p)$. At each fixed cutoff $M$, the proof of YTZU gives $\mathbb EZ_M/N\to\theta_M(p)$. YCHK now makes any fixed positive deviation from this mean exponentially unlikely in $N$. Choose $M\ge2$ so that $\theta_M(p)<\rho+a/8$. For large $n$,</p>
<div class="math-display">$$\mathbb EZ_M/N<\rho+a/4,\qquad M/N<a/4.$$</div>
<p>The bound $L_1\le M+Z_M$ gives the exponential upper tail. If $p\le1/(d-1)$, then $\rho=0$ and $L_2\le L_1$, proving the whole assertion.</p>
<p>Suppose $p>1/(d-1)$. Choose $1/(d-1)<p_1<p$ with $\rho_d(p_1)>\rho-a/8$, and then</p>
<div class="math-display">$$0<\delta<\min\{\rho_d(p_1)/8,a/8\},\qquad
q=\frac{p-p_1}{1-p_1}.$$</div>
<p>Fix $M\ge2\log2/\kappa$, where $\kappa$ is the sprinkling constant from 9906 for $\delta,q$, increasing $M$ to an integer at least two if necessary. The first-round mass $W=Z_M(p_1)$ has expectation at least $(\rho_d(p_1)-\delta/2)N$ for large $n$. YCHK gives</p>
<div class="math-display">$$\mathbb P\bigl(W<(\rho_d(p_1)-\delta)N\bigr)\le Ce^{-cN}.$$</div>
<p>On the complementary event, $W>3\delta N$. Conditional on the first round, NVCH then puts more than $W-\delta N$ vertices in one final component except with probability $e^{-\kappa N/2}$. Its size exceeds $(\rho_d(p_1)-2\delta)N>(\rho-a/2)N$. This proves the lower tail for every fixed tolerance, including when $p=1$.</p>
<p>For the second component choose another fixed $M$ with $\theta_M(p)<\rho+a/8$. Except on an exponentially unlikely event, $Z_M/N<\rho+a/4$, $L_1/N>\rho-a/4$, and $L_1\ge M$. The last assertion follows from the just-proved lower bound with a tolerance smaller than $\rho/2$. If $L_2\ge aN$, both largest components contribute to $Z_M$ for large $n$, contradicting</p>
<div class="math-display">$$Z_M/N\ge L_1/N+a>\rho+3a/4.$$</div>
<p>A finite union of the failure events has the required bound. The cutoffs and the smaller percolation parameter were fixed before taking $n\to\infty$.</p>

## The neighbourhood seen from the giant {#section-expander-local-profile}

<p>Retain the hypotheses of YTZU and fix $p>1/(d-1)$. Choose one largest component $C_1$ by a deterministic tie rule. For a fixed integer $R\ge0$, let $f$ be any isomorphism-invariant function of a finite rooted radius-$R$ graph, with values in $[0,1]$. Here the radius is measured using open paths. Write</p>
<div class="math-display">$$A_f=\mathbb E_p^{T_d}\left[f(B_{C(o)}(o,R))\mathbf1_{\{|C(o)|=\infty\}}\right],\qquad
S_f=\sum_{v\in C_1}f(B_{C_1}(v,R)).$$</div>

<a id="tag-OH6B" data-assertion="theorem" data-title="The empirical local profile of the giant converges to percolation on the regular tree conditioned to survive"></a>
<p>For each fixed $f$ and $a>0$, there are $c,C>0$ such that, for all sufficiently large $n$,</p>
<div class="math-display">$$\mathbb P_p\left(\left|\frac{S_f}{N_n}-A_f\right|\ge a\right)\le Ce^{-cN_n}.$$</div>
<p>In particular, in probability and mean absolute error,</p>
<div class="math-display">$$\frac{S_f}{N_n}\longrightarrow A_f,\qquad
\frac{S_f}{|C_1|}\longrightarrow
\mathbb E_p^{T_d}\left[f(B_{C(o)}(o,R))\mid |C(o)|=\infty\right].$$</div>
<p>The normalized second quantity also has exponentially small deviations of any fixed positive size. Thus a uniformly chosen vertex of the giant has the local law of the tree cluster conditioned to be infinite, in the empirical sense expressed by these formulas.</p>
<p><em>Proof.</em> Evaluate $f$ at every vertex of the full percolated graph, and use these values in $F_{M,f}$ from YCHK. The open radius-$R$ ball is determined by the bonds in the host radius-$R$ ball. The cutoff event is determined in host radius $M-1$. Consequently local convergence gives</p>
<div class="math-display">$$\frac{\mathbb EF_{M,f}}N\longrightarrow
A_{M,f}:=\mathbb E_p^{T_d}\left[f(B_{C(o)}(o,R))\mathbf1_{\{|C(o)|\ge M\}}\right].$$</div>
<p>Moreover $0\le A_{M,f}-A_f\le\theta_M(p)-\rho$. On the event $L_1\ge M$, every vertex of $C_1$ contributes to $F_{M,f}$, and the contribution from the other large components is at most their total mass:</p>
<div class="math-display">$$0\le F_{M,f}-S_f\le Z_M-L_1.$$</div>
<p>Choose $0<\eta<\min\{a/6,\rho/4\}$, then fix $M\ge2$ with $\theta_M(p)-\rho<\eta$. For all sufficiently large $n$, YCHK and UPQ2 show that, outside an event of probability $Ce^{-cN}$,</p>
<div class="math-display">$$\left|F_{M,f}/N-A_{M,f}\right|<\eta,\qquad
Z_M/N<\theta_M(p)+\eta,\qquad L_1/N>\rho-\eta,\qquad L_1\ge M.$$</div>
<p>The expectation limits absorb half of each concentration tolerance. On this event, $(Z_M-L_1)/N<3\eta$ and $|F_{M,f}/N-A_f|<2\eta$, so $|S_f/N-A_f|<5\eta<a$. This proves the first bound.</p>
<p>Since $\rho>0$, UPQ2 also makes $L_1/N<\rho/2$ exponentially unlikely. On its complement, division is uniformly continuous on the bounded pairs $(S_f/N,L_1/N)$, which gives the normalized assertion and its exponential tail. Both normalized variables lie in $[0,1]$, so probability convergence implies convergence in mean absolute error.</p>

## Degrees, edges and cycle excess of the giant {#section-expander-degrees}

<p>Continue at a fixed $p>1/(d-1)$ and write $r_p=u_p^{d-1}$ for the extinction probability of the descendants beyond an open root bond. Let $D_k$ count vertices of open degree $k$ in $C_1$, let $E_1$ be its number of open edges, and let $X_1=E_1-L_1+1$ be its cycle excess.</p>

<a id="tag-VSGH" data-assertion="corollary" data-title="The giant degree profile determines its edge density and cubic near-threshold cycle-excess density"></a>
<p>Define $\alpha_0=0$ and, for $1\le k\le d$,</p>
<div class="math-display">$$\alpha_k=\binom dk p^k(1-p)^{d-k}(1-r_p^k),\qquad
\eta_d(p)=\frac{dp}{2}(1-r_p^2),\qquad \xi_d(p)=\eta_d(p)-\rho_d(p).$$</div>
<p>Then $D_k/N_n\to\alpha_k$, $E_1/N_n\to\eta_d(p)$ and $X_1/N_n\to\xi_d(p)$ in probability and mean absolute error. Joint deviations of these finitely many normalized quantities by any fixed positive tolerance have probability at most $Ce^{-cN_n}$. In particular the degree distribution within the giant tends to $(\alpha_k/\rho_d(p))_{k=0}^d$.</p>
<p>For fixed $d$, the limiting densities themselves satisfy, as $\varepsilon=(d-1)p-1\downarrow0$,</p>
<div class="math-display">$$\rho_d(p)=\frac{2d}{d-2}\varepsilon+O(\varepsilon^2),\qquad
\xi_d(p)=\frac{2d(d-1)}{3(d-2)^2}\varepsilon^3+O(\varepsilon^4).$$</div>
<p>These are expansions of the fixed-parameter limits. They do not assert the same asymptotics for a sequence $p=p_n$ approaching criticality with $n$.</p>
<p><em>Proof.</em> Apply OH6B to the indicator that the root has open degree $k$. On the tree this degree is $\operatorname{Bin}(d,p)$. Given the $k$ open bonds, the $k$ descendant branches are independent and all die with probability $r_p^k$. This gives $\alpha_k$, including $\alpha_0=0$. Every open edge incident to a vertex in $C_1$ stays within $C_1$, so $2E_1=\sum_k kD_k$. The binomial identities and $1-p+pr_p=u_p$ give</p>
<div class="math-display">$$\sum_{k=0}^d\alpha_k=1-u_p^d=\rho_d(p),\qquad
\sum_{k=0}^d k\alpha_k=dp\left[1-r_p(1-p+pr_p)^{d-1}\right]
=dp(1-r_p^2).$$</div>
<p>This proves the edge and excess limits. The finite union bound gives the exponential statements, absorbing the deterministic $1/N$ in the excess. Bounded degree makes all normalized quantities uniformly bounded, giving convergence in mean absolute error.</p>
<p>The edge formula has a direct interpretation: after deleting a specified tree edge, its open state puts it in an infinite component exactly when <em>at least one</em> of the two endpoint branches is infinite. The endpoint failures are independent with probability $r_p$ each, hence the factor $p(1-r_p^2)$. Requiring both branches would instead give $p(1-r_p)^2$ and a different event. The author PDF's prose after (2.4) is recorded in the <a href="/errata/krivelevich-lubetzky-sudakov-expanders/#edge-union-explanation">provisional erratum</a>; its displayed union and final edge-density formula already have the intended meaning.</p>
<p>For the expansions set $t=1-u_p$. The fixed-point equation becomes</p>
<div class="math-display">$$t=p\bigl[1-(1-t)^{d-1}\bigr],\qquad
t=\frac{2}{d-2}\varepsilon+O(\varepsilon^2).$$</div>
<p>The second identity follows by dividing by $t>0$, expanding the polynomial and using $t\to0$ as $p\downarrow1/(d-1)$: any subsequential limit of $u_p$ solves the critical fixed-point equation, whose only root in $[0,1]$ is one. Also $r_p=1-t/p$, so</p>
<div class="math-display">$$\eta_d(p)=dt-\frac d{2p}t^2,\qquad
\rho_d(p)=dt-\frac{d(d-1)}2t^2+\frac{d(d-1)(d-2)}6t^3+O(t^4).$$</div>
<p>Subtract and use $(d-1)-1/p=(d-1)\varepsilon/(1+\varepsilon)$. The quadratic and cubic terms give</p>
<div class="math-display">$$\xi_d(p)=\frac d2\left((d-1)-\frac1p\right)t^2
-\frac{d(d-1)(d-2)}6t^3+O(t^4)
=\frac{2d(d-1)}{3(d-2)^2}\varepsilon^3+O(\varepsilon^4),$$</div>
<p>while $\rho_d(p)=dt+O(t^2)$ gives its first-order expansion.</p>
<p>The edge and degree formulas agree with <a href="https://www.cs.tau.ac.il/~krivelev/expperc.pdf">Krivelevich–Lubetzky–Sudakov, Theorems 1 and 2.1</a>. The local-profile argument above proves these conclusions under the weaker local-tree assumption already used in YTZU. It does not establish the corresponding 2-core laws or a bound uniform through the critical window.</p>


## Expansion after reserving a sparse set of edges {#section-expander-thick-sets}

<p>Let $G$ have $N\ge1$ vertices, maximum degree at most an integer $d\ge2$, and edge expansion at least $h>0$. Call a vertex set <em>$k$-thick</em> if it is a union of disjoint sets, each connected in $G$ and containing at least $k$ vertices. Independently colour each host edge blue with probability $\vartheta$ and red otherwise, and write $G_r$ for the graph of red edges.</p>

<a id="tag-0ATK" data-assertion="proposition" data-title="A sparse independent edge reservation preserves expansion of all macroscopic thick sets"></a>
<p>Fix $0<\delta\le1/2$ and assume</p>
<div class="math-display">$$0<\vartheta\le\frac14(8d^2)^{-2/h}.$$</div>
<p>Choose an integer $k\ge2$ so large that $(ek/\delta)^{1/k}\le2$. Except on an event of probability at most $\min\{1,2^{1-\delta N}\}$, every $k$-thick set $S$ with $\delta N\le|S|\le N/2$ satisfies</p>
<div class="math-display">$$|\partial_{G_r}S|\ge\frac h2|S|.$$</div>
<p><em>Proof.</em> A connected set of $a$ vertices containing a prescribed root has a spanning tree whose depth-first traversal has length $2(a-1)$. Choose one such traversal canonically, using fixed vertex and neighbour orders. Its walk determines the set, so there are at most $d^{2(a-1)}$ possibilities.</p>
<p>For a thick set of size $s$, choose its $j\le s/k$ roots in their fixed order, then its positive block sizes summing to $s$, and then the rooted connected blocks. There are at most $2^s$ choices of sizes for each $j$, so the number of such sets is at most</p>
<div class="math-display">$$2^s d^{2s}\sum_{j=0}^{\lfloor s/k\rfloor}\binom Nj
\le\left[2d^2(ek/\delta)^{1/k}\right]^s\qquad(s\ge\delta N).$$</div>
<p>For the last inequality, if $m=\lfloor s/k\rfloor\ge1$, use $\sum_{j\le m}\binom Nj\le(eN/m)^m$ and the fact that $x\log(eN/x)$ is increasing on $[1,N]$; if $m=0$ no nonempty thick set exists.</p>
<p>For a fixed $S$ in the stated range let $b=|\partial_GS|\ge hs$. If its red boundary is smaller than $hs/2$, more than half of its $b$ boundary edges must be blue. The probability is at most $2^b\vartheta^{b/2}\le(2\sqrt\vartheta)^{hs}$. Our choices make</p>
<div class="math-display">$$2d^2(ek/\delta)^{1/k}(2\sqrt\vartheta)^h\le\frac12.$$</div>
<p>Summing $2^{-s}$ over $s\ge\lceil\delta N\rceil$ proves the assertion. The thickness is measured in the original host graph, not in the random red graph.</p>

## Sprinkling without using the reserved edges {#section-expander-red-sprinkling}

<a id="tag-S8OP" data-assertion="proposition" data-title="Red-only sprinkling coalesces large clusters while leaving the reserved blue edges unused"></a>
<p>Fix a colouring for which the conclusion of 0ATK holds. Let $\omega_0$ be any configuration using only red edges. For an integer $L\ge k$, let $U$ be the union of its components of size at least $L$, and write $W=|U|$. Sprinkle independent Bernoulli-$q$ bonds only on red edges, where $0<q\le1$, and set</p>
<div class="math-display">$$\ell_r=\left\lceil\frac{2d}{h\delta}\right\rceil,
\qquad \kappa_r=\frac{h\delta}{4}q^{\ell_r}.$$</div>
<p>If $W\ge3\delta N$, then the probability that no final red component contains more than $W-\delta N$ vertices of $U$ is at most</p>
<div class="math-display">$$\min\left\{1,\exp\left[N\left(\frac{\log2}{L}-\kappa_r\right)\right]\right\}.$$</div>
<p><em>Proof.</em> Consider a partition of the initial large components into unions $A,B$, both of size at least $\delta N$. Take a minimum red-edge cut separating them, and choose its smaller side $S$, containing one of the terminal unions, say $A$. Remove from $S$ every component of $G_r[S]$ that misses $A$. This does not increase the red cut, keeps all of $A$, and leaves $|S|\le N/2$.</p>
<p>The remaining $S$ is $k$-thick in $G$. Indeed every red component in it meets $A$, and every vertex of $A$ belongs to a whole initial component of size at least $L$, contained in $S$ and connected in $G$. Hence every component of $G[S]$ contains such a block and has size at least $L\ge k$. Also $|S|\ge\delta N$. Its red boundary therefore has size at least $h\delta N/2$.</p>
<p>The cut and path argument of 9906 now gives at least $h\delta N/4$ edge-disjoint red $A$–$B$ paths of length at most $\ell_r$. Independent sprinkling misses all these paths with probability at most $e^{-\kappa_rN}$. There are at most $2^{N/L}$ partitions. The final-component weight argument in NVCH then puts more than $W-\delta N$ of the selected vertices in one red component.</p>

## The edges of the giant's 2-core {#section-expander-core-edges}

<p>The <em>2-core</em> $K(H)$ of a finite graph is the unique maximal induced subgraph with minimum degree at least two, obtained by repeatedly deleting vertices of degree zero or one. A 2-core can contain bridges joining cyclic pieces; membership in the 2-core is not the same as lying on a cycle.</p>
<p>Return to the locally tree-like $d$-regular expanding sequence of YTZU, with fixed $d\ge3$ and $p>1/(d-1)$. Write $H=G_n(p)$, $N=N_n$, and $K_i=K(C_i)$ for the cores of its components in decreasing component-size order. For an integer $M\ge1$ define the local edge set</p>
<div class="math-display">$$\mathcal E_M(H)=\{xy\in E(H):|C_x(H\setminus\{xy\})|\ge M,
\ |C_y(H\setminus\{xy\})|\ge M\}.$$</div>
<p>Let $r_p=u_p^{d-1}$ as before, and set $\eta_2(p)=dp(1-r_p)^2/2$.</p>

<a id="tag-TGLZ" data-assertion="theorem" data-title="The giant 2-core has the tree-predicted edge density and is approximated by two large deletion clusters"></a>
<p>The normalized edge count $|E(K_1)|/N$ converges to $\eta_2(p)$ in probability and mean absolute error. Every fixed positive deviation has probability at most $Ce^{-cN}$. More precisely, for every $a>0$, all sufficiently large fixed cutoffs $M$ admit $c,C>0$ such that, for all sufficiently large $n$,</p>
<div class="math-display">$$\mathbb P_p\left(
|\mathcal E_M(H)\mathbin\triangle E(K_1)|>aN
\ \text{or}\ \sum_{i\ge2}|E(K_i)|>aN
\ \text{or}\ |\{e\in E(K_1):e\text{ is a bridge of }K_1\}|>aN
\right)\le Ce^{-cN}.$$</div>
<p><em>Proof.</em> Let $s_M(t)$ be the probability that the root cluster in a rooted $(d-1)$-ary tree, with bond parameter $t$, has at least $M$ vertices. Then $s_M(t)\downarrow1-r_t$. For a host edge whose sufficiently large fixed neighbourhood is a tree, the two cutoff events after deleting the edge depend on disjoint sets of bonds. Local convergence therefore gives</p>
<div class="math-display">$$\frac{\mathbb E_p|\mathcal E_M(H)|}{N}
\longrightarrow\frac{dp}{2}s_M(p)^2.$$</div>
<p>This count has exponential concentration about its mean at every fixed tolerance on scale $N$. For example apply YCHK with cutoff one to $f_v=d^{-1}\deg_{\mathcal E_M}(v)$, which is determined in a fixed host ball; its sum is $2|\mathcal E_M|/d$.</p>
<p>There is also a deterministic upper comparison with all the cores. If an endpoint has a tree host neighbourhood of radius $2M+2$, a core edge incident to it has at least $M$ vertices accessible from each endpoint after that edge is removed. To see this, extend a nonbacktracking path inside the minimum-degree-two core away from the removed edge. A repetition before reaching $M$ vertices would give a cycle in that tree neighbourhood. The exceptional host vertices are $o(N)$, so</p>
<div class="math-display">$$\left|\bigcup_i E(K_i)\setminus\mathcal E_M(H)\right|=o(N)$$</div>
<p>uniformly over the percolation configurations, for each fixed $M$. Taking $M$ large gives the exponential upper bound $\sum_i|E(K_i)|\le(\eta_2(p)+a)N$ for any fixed $a>0$ and large $n$.</p>
<p>For the lower bound we construct cycles in the giant. Choose a small blue density $\vartheta$ satisfying 0ATK and a first-round parameter $p_0<p$ so that</p>
<div class="math-display">$$p_r=(1-\vartheta)p_0>\frac1{d-1}.$$</div>
<p>Colour the edges independently of independent first-round $p_0$ bonds and second-round $q=(p-p_0)/(1-p_0)$ bonds. Their union is the full $p$ configuration $H$, independent of the colours. The red first round has parameter $p_r$, not $p_0$.</p>
<p>Fix $0<\delta<\min\{1/2,\rho_d(p_r)/8\}$. Let $k$ be supplied by 0ATK and choose a fixed integer $L\ge\max\{k,2\log2/\kappa_r,2\}$. The mass $W$ in red first-round components of size at least $L$ is at least $\rho_d(p_r)N/2$ except with exponentially small probability, by YCHK and local convergence. Thus $W>3\delta N$. The colour event in 0ATK and S8OP give a final red component $C$ containing all but fewer than $\delta N$ of those vertices, except with exponentially small probability.</p>
<p>The component $C$ has at least $\rho_d(p_r)N/3$ vertices. By UPQ2 the full $p$ component containing it is the largest component $C_1$, outside another exponentially unlikely event.</p>
<p>Let $Q$ count blue edges which are open in the first round and whose two endpoints each have a red first-round cluster of size at least $L$. Conditional on a specified edge being blue, its endpoint clusters use only other edges, with parameter $p_r$. On a tree neighbourhood they are independent. Hence</p>
<div class="math-display">$$\frac{\mathbb EQ}{N}\longrightarrow
\frac d2\vartheta p_0 s_L(p_r)^2
\ge\frac d2\vartheta p_0(1-r_{p_r})^2.$$</div>
<p>For each fixed $L$, $Q$ also has exponential concentration at scale $N$. Reveal the independent colour and first-round Bernoulli variables, two per host edge. Changing one variable affects only edge indicators within a fixed host distance depending on $L$, so a bounded number depending on $d,L$. The conditional exponential-moment proof of YCHK applies to these $2|E|$ independent bits.</p>
<p>At most $d\delta N$ of the $Q$ edges have an endpoint among the selected vertices missed by $C$. Every remaining edge has both endpoints connected by a red path in $C$. Since the edge itself is blue, this path and the edge contain a cycle in $C_1$.</p>
<p>Let $J$ be the number of edges of $C_1$ which lie on cycles, and $B$ the number of those edges coloured blue. Conditional <em>only on the full configuration $H$</em>, $B$ has law $\operatorname{Bin}(J,\vartheta)$, because $H$ and the colours are independent. Thus, for each fixed $t>0$,</p>
<div class="math-display">$$B\le\vartheta J+tN$$</div>
<p>except with exponentially small probability. We use this unconditional failure estimate together with the earlier ones; we do not condition the binomial assertion on the good-colouring event. Combining it with $B\ge Q-d\delta N$ and the lower concentration bound for $Q$ gives</p>
<div class="math-display">$$\frac JN\ge\frac d2p_0(1-r_{p_r})^2-\frac{2t+d\delta}{\vartheta}$$</div>
<p>with exponentially small failure probability, for large $n$.</p>
<p>Given a target error, first take $\vartheta$ small and $p_0$ close to $p$, so that continuity of the supercritical tree survival probability makes the first term as close as desired to $\eta_2(p)$. Then choose $\delta,t$ small relative to $\vartheta$ times that error, and only afterwards choose $k,L$. All are fixed before $n\to\infty$. We have proved $J\ge(\eta_2(p)-a)N$ with exponentially small failure probability for every $a>0$. Since $J\le|E(K_1)|$, the edge-density limit follows from the upper bound.</p>
<p>Finally let $A=\bigcup_iE(K_i)$ and $K=E(K_1)$. For fixed large $M$, $|A\setminus\mathcal E_M|=o(N)$, while $|\mathcal E_M|$ and $|K|$ are each within any prescribed small error of $\eta_2(p)N$, with exponential probability bounds. The identity</p>
<div class="math-display">$$|\mathcal E_M\mathbin\triangle K|
=|\mathcal E_M|-|K|+2|K\setminus\mathcal E_M|$$</div>
<p>gives the symmetric-difference estimate. Also $|A\setminus K|\le|\mathcal E_M\setminus K|+o(N)$, which bounds the other cores. An edge of a finite graph is a bridge exactly when it lies on no cycle. Every cycle of $C_1$ lies in $K_1$, so the bridges of $K_1$ number $|K|-J=o(N)$ with the same type of bound. Uniform boundedness by $dN/2$ gives convergence in mean absolute error.</p>
<p>The reduced red parameter in the expectation for $Q$ repairs an intermediate lower bound in the author proof. The <a href="/errata/krivelevich-lubetzky-sudakov-expanders/#red-first-round-parameter">provisional erratum</a> records the parameter correction and its effect on the proof; the fixed-parameter 2-core theorem is preserved.</p>

## Vertex and degree densities in the 2-core {#section-expander-core-profile}

<a id="tag-2K74" data-assertion="corollary" data-title="The giant 2-core has the binomial surviving-branch degree profile and quadratic near-threshold density"></a>
<p>Under the assumptions of TGLZ, put $z=p(1-r_p)=1-u_p$, and for $2\le j\le d$ let $D^{(2)}_j$ count degree-$j$ vertices in $K_1$. Then, jointly in probability and mean absolute error,</p>
<div class="math-display">$$\frac{D^{(2)}_j}{N}\longrightarrow
\beta_j=\binom dj z^j(1-z)^{d-j},\qquad
\frac{|V(K_1)|}{N}\longrightarrow\rho_2(p)=1-u_p^d-dz u_p^{d-1}.$$</div>
<p>Each joint deviation of fixed positive size has probability at most $Ce^{-cN}$. The total number of vertices in the other component cores is $o(N)$ with the same exponential fixed-tolerance bounds. The limiting densities satisfy</p>
<div class="math-display">$$\eta_2(p)-\rho_2(p)=\eta_d(p)-\rho_d(p)=\xi_d(p).$$</div>
<p>For fixed $d$ and $\varepsilon=(d-1)p-1\downarrow0$, after taking the graph-size limit,</p>
<div class="math-display">$$\rho_2(p)=\frac{2d(d-1)}{(d-2)^2}\varepsilon^2+O(\varepsilon^3),\qquad
\eta_2(p)=\frac{2d(d-1)}{(d-2)^2}\varepsilon^2+O(\varepsilon^3).$$</div>
<p>Their difference has the cubic expansion in VSGH.</p>
<p><em>Proof.</em> For fixed $M$, the degree at a vertex in the edge set $\mathcal E_M$ is a local function. Its empirical frequency at any prescribed value concentrates exponentially by YCHK with cutoff one. Local tree convergence identifies its expectation with that on $T_d$.</p>
<p>On the tree, as $M\to\infty$, an incident edge belongs to $\mathcal E_M$ in the limit precisely when it is open and both sides after its deletion are infinite. Let $Z$ be the number of incident open branches which survive. These branches are independent, so $Z\sim\operatorname{Bin}(d,z)$. If $Z\ge2$, exactly those $Z$ edges satisfy the two-sided condition; if $Z\le1$, none does. Thus the limiting local degree frequency at $j\ge2$ is $\beta_j$.</p>
<p>The degrees in $\mathcal E_M$ and $K_1$ can differ at no more than $2|\mathcal E_M\mathbin\triangle E(K_1)|$ vertices. Choose a sufficiently large fixed $M$ for the local expectation error and TGLZ, then let $n\to\infty$. This proves each degree law with exponential deviations. Summing over $j\ge2$ gives $\rho_2=\mathbb P(Z\ge2)$. Every other nonempty core has minimum degree at least two, hence at least as many edges as vertices; TGLZ therefore bounds its total vertex contribution. All normalized counts are bounded, giving the asserted mean limits.</p>
<p>Finally</p>
<div class="math-display">$$\frac12\sum_{j=2}^d j\beta_j
=\frac{dz}{2}(1-u_p^{d-1})=\eta_2(p),\qquad
\rho_d(p)-\rho_2(p)=dzr_p
=\eta_d(p)-\eta_2(p).$$</div>
<p>This proves the excess identity. Since $z=2\varepsilon/(d-2)+O(\varepsilon^2)$ by VSGH, expansion of the binomial probability $\mathbb P(Z\ge2)$ gives $\rho_2=\binom d2z^2+O(z^3)$, and $\eta_2=dz^2/(2p)$ gives the other quadratic term.</p>
<p>The argument reconstructs <a href="https://www.cs.tau.ac.il/~krivelev/expperc.pdf">Krivelevich–Lubetzky–Sudakov, Section 2.2</a>, retaining the corrected red parameter and allowing a vanishing fraction of non-tree host neighbourhoods. All bounds here are at fixed $p>1/(d-1)$; they give no estimate uniform through the critical window.</p>


## Thinning after choosing a deletion set {#section-expander-thinning-deletion}

<p>Write $L_1(F)$ for the largest component order of a finite graph $F$, with $L_1(\varnothing)=0$. Vertex deletion removes the vertices as well as their incident edges.</p>

<a id="tag-58KB" data-assertion="proposition" data-title="Independent thinning pays only for the edges touching a configuration-dependent deletion set"></a>
<p>Let $G$ be a finite simple graph of maximum degree at most $d$, let $0<p_0<p\le1$, and let $k\ge0$ be an integer. For every real $t\ge1$,</p>
<div class="math-display">$$\mathbb P_p\bigl(\exists S\subseteq V(G): |S|\le k,\ L_1(G(p)\setminus S)\le t\bigr)
\le (1-p_0/p)^{-dk}\,\mathbb P_{p_0}\bigl(L_1(G(p_0))\le t\bigr).$$</div>
<p><em>Proof.</em> Sample $H=G(p)$ and independently retain each of its edges with probability $\alpha=p_0/p$, obtaining $H_0$ with law $G(p_0)$. If the event on the left occurs, choose one witnessing $S$ by a fixed ordering of the finitely many subsets. Conditional on the entire $H$, this choice is fixed. At most $dk$ open edges touch $S$, so the probability that thinning removes all of them is <em>at least</em> $(1-\alpha)^{dk}$.</p>
<p>On that event, the vertices of $S$ are isolated in $H_0$, and each other component of $H_0$ lies in a component of $H\setminus S$. Thus $L_1(H_0)\le t$; the assumption $t\ge1$ accounts for the isolated vertices. Integrate the conditional lower bound and rearrange. There is no union bound over choices of $S$.</p>
<p>The direction of this conditional probability bound corrects a sentence in <a href="https://www.cs.tau.ac.il/~krivelev/expperc.pdf">Krivelevich–Lubetzky–Sudakov, the proof of Theorem 4.1</a>. The subsequent displayed comparison in that proof already uses the lower bound. The <a href="/errata/krivelevich-lubetzky-sudakov-expanders/#thinning-deletion-probability-direction">provisional erratum</a> records the correction.</p>

## The giant survives arbitrary small vertex deletions {#section-expander-resilience}

<p>Continue with the locally tree-like $d$-regular uniformly expanding sequence of YTZU, at a fixed parameter $1/(d-1)<p\le1$. Put $\rho=\rho_d(p)>0$ and $N=|V(G_n)|$. All constants below are fixed before $n\to\infty$.</p>

<a id="tag-P3AV" data-assertion="theorem" data-title="Deleting a small proportion of vertices leaves almost all of the expander giant connected"></a>
<p>For every $0<a<\rho$ there are $\delta,c,C>0$ such that, for all sufficiently large $n$, with probability at least $1-Ce^{-cN}$, simultaneously for every $S\subseteq V(G_n)$ with $|S|\le\delta N$, some component $D$ of $C_1(G_n(p))\setminus S$ satisfies</p>
<div class="math-display">$$|D|\ge |C_1(G_n(p))|-aN.$$</div>
<p>In particular, there are $\delta_*,c_*,C_*>0$ such that, with probability at least $1-C_*e^{-c_*N}$, no set of at most $\delta_*N$ vertices is a balanced separator of the giant. Here a balanced separator of a graph $F$ of order $m$ means a set $S$ for which $V(F)\setminus S$ can be partitioned as $A\cup B$, with no edge between $A$ and $B$ and $|A|,|B|\le2m/3$.</p>
<p><em>Proof.</em> Choose $p_0\in(1/(d-1),p)$ close enough to $p$ that $\rho_d(p_0)>\rho-a/4$, and set $b=\rho-a/2>0$. The exponential estimate UPQ2 gives constants $c_0,C_0>0$ with</p>
<div class="math-display">$$\mathbb P_{p_0}(L_1\le bN)\le C_0e^{-c_0N}$$</div>
<p>for all sufficiently large $n$. Apply 58KB with $k=\lfloor\delta N\rfloor$ and $t=bN\ge1$. Choosing $\delta>0$ so small that</p>
<div class="math-display">$$d\delta\log\frac1{1-p_0/p}<\frac{c_0}{2}$$</div>
<p>makes the probability of any such $S$ with $L_1(G_n(p)\setminus S)\le bN$ at most $C_0e^{-c_0N/2}$.</p>
<p>Outside another exponentially unlikely event, UPQ2 gives $L_1\le(\rho+a/4)N$ and $L_2<bN$. Hence the component larger than $bN$ left after any permitted deletion must lie in the original giant. It misses fewer than $3aN/4$ of that giant's vertices, proving the first assertion.</p>
<p>For the separator assertion take $a=\rho/10$ and also use $L_1\ge\rho N/2$, again outside exponentially small probability. The surviving component then has more than $2L_1/3$ vertices. Such a component cannot lie in either side of a balanced separation. A set of vertices chosen adversarially after seeing the entire percolation configuration is covered by the same argument.</p>

## A path which separates a finite graph {#section-expander-dfs-separator}

<a id="tag-PMXD" data-assertion="proposition" data-title="Every finite connected graph has a simple path whose vertex set is a balanced separator"></a>
<p>Every finite connected graph $F$ with $m\ge2$ vertices has a simple path $P$ such that its vertex set is a balanced separator. Consequently, if $F$ has no balanced separator of at most $k$ vertices, where $k$ is a nonnegative integer, it has a simple path of at least $k$ edges.</p>
<p><em>Proof.</em> Run depth-first search from any root, keeping the current recursion stack $S$, the finished vertices $A$, and the unseen vertices $B$. The stack is a simple path. There is no edge from $A$ to $B$: before a vertex is finished, search has visited each of its neighbours.</p>
<p>Stop immediately after the number of finished vertices first becomes $\lceil m/3\rceil$. This number increases one at a time. Since $1\le\lceil m/3\rceil<m$ and $F$ is connected, the stack is nonempty. Moreover</p>
<div class="math-display">$$|A|=\lceil m/3\rceil\le2m/3,
\qquad |B|\le m-\lceil m/3\rceil\le2m/3.$$</div>
<p>Thus $S$ is the required separator. If every balanced separator has more than $k$ vertices, this path has more than $k$ vertices and therefore at least $k$ edges.</p>

## Closing a long path with a short connection {#section-expander-cycle-connector}

<a id="tag-F067" data-assertion="proposition" data-title="A bounded-length connector between distant points of a path forces a long cycle even when it meets the path again"></a>
<p>Let $P=(v_0,\ldots,v_m)$ be a simple path in a simple graph. Suppose a simple path $Q$ of at most $\ell\ge1$ edges joins $v_a$ to $v_b$, where $D=|b-a|>\ell$. Then $P\cup Q$ contains a simple cycle of at least $D/\ell$ edges. No restriction is imposed on the other intersections of $Q$ with $P$.</p>
<p><em>Proof.</em> List the successive vertices of $Q$ which lie on $P$, and let their indices along $P$ be $i_0=a,i_1,\ldots,i_s=b$. Consecutive intersections use at least one edge of $Q$, so $s\le\ell$. The triangle inequality gives</p>
<div class="math-display">$$D\le\sum_{j=1}^s|i_j-i_{j-1}|.$$</div>
<p>Some consecutive pair therefore has index difference at least $D/\ell>1$. The intervening segment of $Q$ has no internal vertex on $P$. Together with the segment of $P$ between its endpoints, it forms a simple cycle. The latter segment already has at least $D/\ell$ edges; an edge shared with $P$ cannot be the chosen connector segment, since then the index difference would be one.</p>

## Linear paths and cycles in the giant {#section-expander-linear-cycles}

<a id="tag-8NPK" data-assertion="theorem" data-title="The fixed-supercritical expander giant and its 2-core contain a cycle of linear length with exponential probability bounds"></a>
<p>Under the hypotheses of P3AV, there are $\gamma,c,C>0$ such that, for all sufficiently large $n$,</p>
<div class="math-display">$$\mathbb P_p\bigl(C_1(G_n(p))\text{ contains a simple cycle with at least }\gamma N\text{ edges}\bigr)
\ge1-Ce^{-cN}.$$</div>
<p>The cycle lies in the giant's 2-core. In particular both the giant and its 2-core contain simple paths of linear length, with exponentially small failure probability.</p>
<p><em>Proof.</em> First, at any fixed supercritical parameter, P3AV and PMXD give a simple path of length at least $\gamma_0N$ in the giant, outside an exponentially unlikely event, for some $\gamma_0>0$. Indeed, a path separator must have more than $\delta_*N$ vertices; for large $N$, its number of edges is at least $\delta_*N/2$.</p>
<p>Choose $p_0\in(1/(d-1),p)$ and apply this observation in the first-round graph $H_0=G_n(p_0)$. Select one resulting path $P=(v_0,\ldots,v_m)$ of length $m\ge\gamma_0N$ using a fixed ordering. Sprinkle independent bonds with probability $q=(p-p_0)/(1-p_0)>0$, obtaining $H$ with law $G_n(p)$.</p>
<p>Take the initial and terminal vertex sets</p>
<div class="math-display">$$A=\{v_0,\ldots,v_{\lfloor m/3\rfloor}\},\qquad
B=\{v_{m-\lfloor m/3\rfloor},\ldots,v_m\}.$$</div>
<p>For sufficiently large $N$ these are disjoint, each with at least $\gamma_0N/3$ vertices. Fix $0<\delta_0\le\min\{\gamma_0/4,1/4\}$ and put $\ell=\lceil d/(h\delta_0)\rceil$, where $h>0$ is the uniform host edge-expansion bound. Conditional on the first round, 9906 supplies edge-disjoint host paths of length at most $\ell$ between $A$ and $B$. The probability that none is entirely open in the sprinkling is at most</p>
<div class="math-display">$$\exp\!\left[-\frac{h\delta_0}{2}q^\ell N\right].$$</div>
<p>Any surviving path $Q$ joins two vertices whose indices along $P$ differ by at least $m/3\ge\gamma_0N/3$. For large $N$ this exceeds $\ell$, so F067 produces a cycle of length at least $\gamma_0N/(3\ell)$. This step allows $Q$ to meet the middle of $P$; it does not assume the sprinkled connector is internally disjoint from the original path.</p>
<p>The full component containing $P\cup Q$ has at least $\gamma_0N$ vertices. UPQ2 at $p$ gives $L_2<\gamma_0N/2$ except with exponentially small probability, so this component is the giant. Every cycle survives leaf deletion and therefore lies in its 2-core. Removing one edge of the cycle leaves a simple path, of linear length after reducing the constant if necessary. Combining the failure estimates proves the claim, including $p=1$, when the sprinkling parameter is one.</p>
<p>This completes the separator, path and cycle argument of <a href="https://www.cs.tau.ac.il/~krivelev/expperc.pdf">Krivelevich–Lubetzky–Sudakov, Section 4</a> for the local-tree hypothesis used here. These are fixed-parameter conclusions. They neither give the optimal cycle-length constant nor a uniform estimate as $p$ approaches the critical point. The source's complete-minor conclusion uses a separate separator theorem and is not claimed here.</p>


## The first exploration components {#section-er-early-start}

<p>Return to $G(N,p)$ with $p=(1+\varepsilon)/N$, where $\varepsilon\to0$ and $R=N\varepsilon^3\to\infty$. The leading-order law <a href="/tag/2KT9/">2KT9</a> does not resolve fluctuations of order $\sqrt{N/\varepsilon}$. To reach that scale we keep the exact deterministic trajectory of the exploration in <a href="/tag/AUTD/">AUTD</a>. Write $A_t$ for the active queue, $C_t$ for the number of components started, $Y_t=A_t-C_t$, and $\Delta_t=\eta_t-\mathbb E(\eta_t\mid\mathcal F_{t-1})$. Put</p>
<div class="math-display">$$r=1-p,\qquad x_t=N-t-Nr^t,\qquad S_t=\sum_{i=1}^t r^{-i}\Delta_i,\qquad Z_t=r^tS_t.$$</div>
<p>The conditional binomial law gives the exact recursion</p>
<div class="math-display">$$Y_t=rY_{t-1}+\varepsilon-p(t-1)-pC_t+\Delta_t.$$</div>
<p>The same recursion without its last two terms defines $x_t$. Subtracting and summing therefore gives</p>
<div class="math-display">$$Y_t=x_t+Z_t-p\sum_{i=1}^t r^{t-i}C_i,\qquad A_t=x_t+Z_t+E_t,\qquad E_t=C_t-p\sum_{i=1}^t r^{t-i}C_i.$$</div>
<p>Monotonicity of $C_i$ and the geometric sum imply $r^tC_t\le E_t\le C_t$. Moreover, $S_t$ is a martingale. Up to time $3\varepsilon N$, its increments have conditional variance at most $8$ for all sufficiently large $N$: the variance of $\Delta_i$ is at most $Np\le2$, and $r^{-i}\le2$. In particular, $\max_{t\le3\varepsilon N}|Z_t|=O_{\mathbb P}(\sqrt{\varepsilon N})$.</p>

<a id="tag-UEXT" data-assertion="proposition" data-title="The barely supercritical exploration reaches its giant after a tight inverse-square time"></a>
<p>Let $t_1=\lfloor\varepsilon N\rfloor$, and let $\tau$ be the last time at or before $t_1$ when $A_t=0$. Then</p>
<div class="math-display">$$C_{t_1}=O_{\mathbb P}(\varepsilon^{-1}),\qquad \tau=O_{\mathbb P}(\varepsilon^{-2}).$$</div>
<p>With probability tending to one, the component being explored at $t_1$ is the unique largest component. If $\sigma=\min\{t\ge t_1:A_t=0\}$, then on this event $L_1=\sigma-\tau$ and $C_\sigma=C_{t_1}$.</p>
<p><em>Proof.</em> For $0\le s\le t_1$, the bound $r^s\le e^{-ps}\le1-ps+(ps)^2/2$ gives</p>
<div class="math-display">$$x_s\ge\varepsilon s-\frac{(1+\varepsilon)^2s^2}{2N}\ge c\varepsilon s,\qquad c=\frac14,$$</div>
<p>once $N$ is large. Reflection of the exploration walk says $C_{t_1}=1-\min_{s<t_1}Y_s$. Since $C_i\le C_{t_1}$ for $i\le t_1$, the exact representation yields</p>
<div class="math-display">$$(1-pt_1)C_{t_1}\le1+\max_{s\le t_1}(-x_s-Z_s)\le1+\max_{s\le t_1}(-c\varepsilon s-S_s)_+.$$</div>
<p>Here $x_s/r^s\ge c\varepsilon s$ and $r^s\le1$ justify the last inequality. For $u\ge1$, apply the martingale maximal inequality first up to time $u\varepsilon^{-2}$, with threshold $u/\varepsilon$, and then on the time ranges from $2^ju\varepsilon^{-2}$ to $2^{j+1}u\varepsilon^{-2}$. On the latter range the event $-c\varepsilon s-S_s>u/\varepsilon$ requires $\max_{i\le2^{j+1}u\varepsilon^{-2}}|S_i|\ge c2^ju/\varepsilon$. Stop all ranges at $t_1$. The variance bound gives probabilities at most $K/u$ and $K/(2^ju)$, respectively. Rounding endpoints changes only the absolute constant $K$. Summing proves</p>
<div class="math-display">$$\mathbb P\!\left(\max_{s\le t_1}(-c\varepsilon s-S_s)>\frac u\varepsilon\right)\le\frac Ku.$$</div>
<p>Since $pt_1\to0$, this proves the bound on $C_{t_1}$. For the start time there is a simpler observation: $E_s\ge0$, so $A_s=0$ implies $S_s\le-x_s/r^s\le-c\varepsilon s$. The same dyadic maximal estimate, starting at $u\varepsilon^{-2}$, bounds the probability of any such zero before $t_1$ by $K/u$. This proves the bound on $\tau$. Finally, the long-excursion argument in <a href="/tag/2KT9/">2KT9</a> puts $t_1$ in the unique giant with probability tending to one and gives $\sigma/(\varepsilon N)\to2$ in probability. No component starts between $t_1$ and its completion. $\square$</p>

## Gaussian fluctuations of the exploration {#section-er-exploration-clt}

<a id="tag-WEV8" data-assertion="proposition" data-title="A Gaussian limit for the barely supercritical exploration martingale"></a>
<p>In the preceding regime, for every deterministic integer sequence $T$ with $T/(\varepsilon N)\to s\in(0,\infty)$,</p>
<div class="math-display">$$\frac{Z_T}{\sqrt T}\ \xrightarrow{\ d\ }\ \mathcal N(0,1).$$</div>
<p><em>Proof.</em> First consider $M_t=\sum_{i\le t}\Delta_i$. If $n_i=N-i+1-A_{i-1}-\mathbf1_{\{A_{i-1}=0\}}$, then conditionally on $\mathcal F_{i-1}$, $\eta_i$ has law $\operatorname{Bin}(n_i,p)$ and</p>
<div class="math-display">$$v_i:=\mathbb E(\Delta_i^2\mid\mathcal F_{i-1})=n_ip(1-p).$$</div>
<p>The queue estimate in <a href="/tag/AUTD/">AUTD</a>, together with the maximal inequality for $M$, gives $\mathbb E A_i\le1+\varepsilon i+K\sqrt T$ for $i\le T$. Since $|v_i-1|\le\varepsilon+Kp+pi+pA_{i-1}$, it follows that</p>
<div class="math-display">$$\frac1T\sum_{i=1}^T\mathbb E|v_i-1|\longrightarrow0.$$</div>
<p>The conditional third absolute moments of $\Delta_i$ are bounded by an absolute constant. Indeed, a binomial variable with mean at most $2$ has third moment at most $2^3+3\cdot2^2+2$, and $|a-b|^3\le4(|a|^3+|b|^3)$.</p>
<p>These estimates also give a direct characteristic-function proof, without assuming independence of the increments. Fix $u\in\mathbb R$, put $a_T=\exp(-u^2/(2T))$, and condition each exponential increment on its past. Taylor's formula gives</p>
<div class="math-display">$$\mathbb E\!\left(e^{iu\Delta_i/\sqrt T}\mid\mathcal F_{i-1}\right)=1-\frac{u^2v_i}{2T}+R_i,\qquad \mathbb E|R_i|\le K_uT^{-3/2}.$$</div>
<p>Multiplying by $e^{iuM_{i-1}/\sqrt T}$ and telescoping against $a_T$ therefore yields</p>
<div class="math-display">$$\left|\mathbb E e^{iuM_T/\sqrt T}-a_T^T\right|\le\frac{u^2}{2T}\sum_{i=1}^T\mathbb E|v_i-1|+K_uT^{-1/2}+K_uT^{-1}\longrightarrow0.$$</div>
<p>The continuity theorem for characteristic functions proves $M_T/\sqrt T\Rightarrow\mathcal N(0,1)$. Finally, martingale orthogonality gives</p>
<div class="math-display">$$\mathbb E|Z_T-M_T|^2=\sum_{i=1}^T(r^{T-i}-1)^2\mathbb E\Delta_i^2\le2T(pT)^2=o(T),$$</div>
<p>because $pT=O(\varepsilon)$. This transfers the limit to $Z_T$. $\square$</p>

## Fluctuations of the complete-graph giant {#section-er-giant-clt}

<a id="tag-UKVG" data-assertion="theorem" data-title="The barely supercritical complete-graph giant has Gaussian fluctuations about the survival-probability center"></a>
<p>Let $\varepsilon=\varepsilon_N>0$, $\varepsilon_N\to0$ and $N\varepsilon_N^3\to\infty$. For $G(N,(1+\varepsilon)/N)$, let $L_1$ be its largest component size and let $\rho=\rho(\varepsilon)$ be the unique positive solution of $1-\rho=e^{-(1+\varepsilon)\rho}$. Then</p>
<div class="math-display">$$\frac{L_1-N\rho}{\sqrt{2N/\varepsilon}}\ \xrightarrow{\ d\ }\ \mathcal N(0,1).$$</div>
<p><em>Proof.</em> Set $\mu_N=-N\log(1-p)$, let $\rho_N>0$ solve $1-\rho_N=e^{-\mu_N\rho_N}$, and put $t_*=N\rho_N$. Thus $x_{t_*}=0$, where $x$ is extended to real times. The identity</p>
<div class="math-display">$$\mu=\frac{-\log(1-\rho_\mu)}{\rho_\mu}=1+\frac{\rho_\mu}{2}+\frac{\rho_\mu^2}{3}+O(\rho_\mu^3)$$</div>
<p>shows that $\rho_\mu\sim2(\mu-1)$ as $\mu\downarrow1$. Since $\mu_N=1+\varepsilon+O(N^{-1})$ and $N\varepsilon\to\infty$,</p>
<div class="math-display">$$t_*\sim2\varepsilon N,\qquad a_N:=-x'(t_*)=1-\mu_N(1-\rho_N)\sim\varepsilon.$$</div>
<p>Use $\tau,\sigma$ from <a href="/tag/UEXT/">UEXT</a>. With probability tending to one, $L_1=\sigma-\tau$ and $\sigma/(\varepsilon N)\to2$. At the completion time, $A_\sigma=0$, while $0\le E_\sigma\le C_\sigma=C_{t_1}=O_{\mathbb P}(\varepsilon^{-1})$. Consequently the exact queue representation gives</p>
<div class="math-display">$$x_\sigma=O_{\mathbb P}(\sqrt{\varepsilon N}),$$</div>
<p>using $\varepsilon^{-1}=o(\sqrt{\varepsilon N})$. On the interval $[7\varepsilon N/4,9\varepsilon N/4]$, the derivative $x'$ is negative and has absolute value bounded above and below by fixed positive multiples of $\varepsilon$, for all sufficiently large $N$. Both $\sigma$ and $t_*$ lie there with probability tending to one. The mean value theorem thus sharpens their separation to</p>
<div class="math-display">$$\sigma-t_*=O_{\mathbb P}(b_N),\qquad b_N=\sqrt{N/\varepsilon}.$$</div>
<p>Let $T=\lfloor t_*\rfloor$. For fixed $K$, the martingale maximal inequality on the deterministic interval $[T-Kb_N,T+Kb_N]$, started at its left endpoint, gives</p>
<div class="math-display">$$\max_{|t-T|\le Kb_N}|Z_t-Z_T|=O_{\mathbb P}(\sqrt{b_N}+pb_N\sqrt{\varepsilon N})=o_{\mathbb P}(\sqrt{\varepsilon N}).$$</div>
<p>The first term bounds increments of $S$; the second bounds the change in the factor $r^t$. Integer rounding has no effect. The ratios vanish because $b_N/(\varepsilon N)=R^{-1/2}\to0$ and $pb_N\to0$. Tightness of $(\sigma-t_*)/b_N$, followed by $K\to\infty$, now gives $Z_\sigma=Z_T+o_{\mathbb P}(\sqrt{\varepsilon N})$.</p>
<p>Since $|x''(t)|\le K/N$ for $t\ge0$, Taylor's formula at $t_*$ yields</p>
<div class="math-display">$$x_\sigma=-a_N(\sigma-t_*)+O_{\mathbb P}(b_N^2/N)=-a_N(\sigma-t_*)+o_{\mathbb P}(\sqrt{\varepsilon N}).$$</div>
<p>Substituting in $0=A_\sigma=x_\sigma+Z_\sigma+E_\sigma$ gives</p>
<div class="math-display">$$\sigma-t_*=\frac{Z_T}{a_N}+o_{\mathbb P}(b_N).$$</div>
<p>By <a href="/tag/UEXT/">UEXT</a>, $\tau=O_{\mathbb P}(\varepsilon^{-2})=o_{\mathbb P}(b_N)$. By <a href="/tag/WEV8/">WEV8</a>, $Z_T/\sqrt T\Rightarrow\mathcal N(0,1)$. The relations $T\sim2\varepsilon N$ and $a_N\sim\varepsilon$ prove the claimed limit with $t_*$ in place of $N\rho$.</p>
<p>To replace the center, differentiate the defining equation:</p>
<div class="math-display">$$\frac{d\rho_\mu}{d\mu}=\frac{\rho_\mu(1-\rho_\mu)}{1-\mu(1-\rho_\mu)}\longrightarrow2\qquad(\mu\downarrow1).$$</div>
<p>This derivative is bounded near $1$, so $\mu_N-(1+\varepsilon)=O(N^{-1})$ implies $N(\rho_N-\rho)=O(1)=o(b_N)$. The centering change is negligible. $\square$</p>
<p>This is the barely supercritical specialization of Bollobás–Riordan's Corollary 2, which they derive from the Pittel–Wormald theorem. Their weighted exploration representation motivates the proof above. The early-start estimate and the characteristic-function calculation are supplied here explicitly. This statement is convergence in distribution; convergence of the centered means or variances requires additional uniform-integrability estimates.</p>

## When the leading-order center suffices {#section-er-giant-centering}

<a id="tag-MEUA" data-assertion="corollary" data-title="The transition between survival-probability and leading-order centering of the barely supercritical giant"></a>
<p>Under the hypotheses of <a href="/tag/UKVG/">UKVG</a>, if $N\varepsilon^5\to b\in[0,\infty)$, then</p>
<div class="math-display">$$\frac{L_1-2\varepsilon N}{\sqrt{2N/\varepsilon}}\ \xrightarrow{\ d\ }\ \mathcal N\!\left(-\frac8{3\sqrt2}\sqrt b,1\right).$$</div>
<p>If $N\varepsilon^5\to\infty$, the same normalized variable tends to $-\infty$ in probability. In particular, centering at $2\varepsilon N$ gives the centered Gaussian limit when $N\varepsilon^5\to0$.</p>
<p><em>Proof.</em> Expanding $1+\varepsilon=-\log(1-\rho)/\rho$ first gives $\rho=2\varepsilon+O(\varepsilon^2)$ and then</p>
<div class="math-display">$$\rho=2\varepsilon-\frac83\varepsilon^2+O(\varepsilon^3),\qquad \frac{N(\rho-2\varepsilon)}{\sqrt{2N/\varepsilon}}=-\frac8{3\sqrt2}\sqrt{N\varepsilon^5}\,(1+O(\varepsilon)).$$</div>
<p>Add this deterministic displacement to the tight, asymptotically standard Gaussian variable in <a href="/tag/UKVG/">UKVG</a>. $\square$</p>


## Exponential bounds for exploration increments {#section-er-exponential-increments}

<p>The logarithmic component law in <a href="/tag/2KT9/">2KT9</a> can also be passed to expectations. This requires control on the exceptional configurations where the usual giant is absent or unusually large. We first obtain that control from the same exploration martingale.</p>

<a id="tag-N9DF" data-assertion="proposition" data-title="A conditional maximal bound for martingales with centered binomial increments"></a>
<p>Suppose $M_0=0$ and each increment $\Delta_i=M_i-M_{i-1}$, conditionally on $\mathcal F_{i-1}$, is a centered binomial variable whose mean before centering is at most $2$. For deterministic integers $s\ge0$, $h\ge1$ within the time horizon and every $u>0$,</p>
<div class="math-display">$$\mathbb P\!\left(\max_{0\le j\le h}|M_{s+j}-M_s|\ge u\,\middle|\,\mathcal F_s\right)\le2\exp\!\left[-\frac18\min\left\{\frac{u^2}{h},u\right\}\right].$$</div>
<p><em>Proof.</em> If the conditional binomial parameters are $n,p$, then for $|\theta|\le1$,</p>
<div class="math-display">$$\mathbb E(e^{\theta\Delta_i}\mid\mathcal F_{i-1})=e^{-\theta np}(1+p(e^\theta-1))^n\le\exp\{np(e^\theta-1-\theta)\}\le e^{2\theta^2}.$$</div>
<p>For $0<\theta\le1$, the process $\exp\{\theta(M_{s+j}-M_s)-2\theta^2j\}$ is therefore a nonnegative supermartingale, also after conditioning on $\mathcal F_s$. Stop at the first crossing of level $u$ by $M_{s+j}-M_s$, or at time $h$. This gives an upper-tail bound $\exp(-\theta u+2\theta^2h)$. Choose $\theta=\min\{u/(4h),1/2\}$. If $u\le2h$ the exponent is $-u^2/(8h)$; otherwise it is at most $-u/4$. Apply the same argument to $-M$ and add the bounds. $\square$</p>

## An upper tail beyond the giant scale {#section-er-global-largest-tail}

<a id="tag-PMEN" data-assertion="proposition" data-title="A cubic exponential upper tail for complete-graph components above the supercritical scale"></a>
<p>There are absolute constants $c,C>0$ such that, for every integer $N\ge2$, every $0\le\varepsilon\le1$, $p=(1+\varepsilon)/N$, and every integer $k$ satisfying</p>
<div class="math-display">$$\max\{16,16\varepsilon N,N^{2/3}\}\le k\le N,$$</div>
<p>the largest component of $G(N,p)$ satisfies</p>
<div class="math-display">$$\mathbb P(L_1\ge k)\le C\exp(-ck^3/N^2).$$</div>
<p><em>Proof.</em> Use the exploration of <a href="/tag/AUTD/">AUTD</a> on its full time interval $0,\ldots,N$. Its conditional means satisfy $\mathbb E(\eta_i-1\mid\mathcal F_{i-1})\le\varepsilon-p(i-1)$, and its martingale increments meet the hypotheses of <a href="/tag/N9DF/">N9DF</a>. If a component of order at least $k$ starts just after time $s$, put $\ell=\lfloor k/2\rfloor$. The component is still active at $s+\ell$, so $Y_{s+\ell}\ge Y_s$. Summing the conditional mean bound gives</p>
<div class="math-display">$$M_{s+\ell}-M_s\ge p\ell s+\frac p2\ell(\ell-1)-\varepsilon\ell\ge\frac{k(s+k)}{32N}.$$</div>
<p>For the last inequality, $p\ge1/N$, $\ell\ge7k/16$, $\ell-1\ge3k/8$ and $\varepsilon N\le k/16$ give the stronger lower bound $\ell(s+k/8)/N$.</p>
<p>Partition the possible start times into intervals $jk\le s<(j+1)k$. Both $s$ and $s+\ell$ then lie in the deterministic interval from $jk$ to $\min\{(j+2)k,N\}$. Hence some component starting in this block can have order at least $k$ only if</p>
<div class="math-display">$$\max_{jk\le t\le\min\{(j+2)k,N\}}|M_t-M_{jk}|\ge\frac{(j+1)k^2}{64N}.$$</div>
<p>Apply N9DF with interval length at most $2k$. Its quadratic term applies since $(j+1)k\le N+k\le2N$. For an absolute $c_0>0$, the probability is at most $2\exp\{-c_0(j+1)^2k^3/N^2\}$. Summing over the blocks, and using $k^3/N^2\ge1$, gives</p>
<div class="math-display">$$\mathbb P(L_1\ge k)\le2\sum_{j\ge0}e^{-c_0(j+1)^2k^3/N^2}\le Ce^{-ck^3/N^2}.$$</div>
<p>The intervals are deterministic; there is no union bound over individual vertices or random component starts. $\square$</p>
<p>In particular, when $0<\varepsilon\le1$ and $R=N\varepsilon^3\ge1$, for $x\ge32$ the choice $k=\lceil x\varepsilon N\rceil$ is admissible unless $k>N$, in which case the event is empty. Thus</p>
<div class="math-display">$$\mathbb P(L_1/(\varepsilon N)\ge x)\le Ce^{-cx^3R},\qquad \mathbb E(L_1/(\varepsilon N))^q\le C_q\quad(q>0).$$</div>
<p>The moment estimate follows by integrating the tail, with the part below $32$ bounded directly. All constants are independent of $N$ and $\varepsilon$ in this range.</p>

## Exponentially unlikely failures of the giant-size law {#section-er-exponential-giant}

<a id="tag-PW6A" data-assertion="theorem" data-title="Fixed relative deviations and nonuniqueness of the barely supercritical giant are exponentially unlikely"></a>
<p>Suppose $\varepsilon\to0$, $R=N\varepsilon^3\to\infty$ and $p=(1+\varepsilon)/N$. For each fixed $0<\delta<1/4$, there are $c_\delta,C_\delta>0$ such that, for all sufficiently large $N$,</p>
<div class="math-display">$$\mathbb P(E_\delta^c)\le C_\delta e^{-c_\delta R},\qquad E_\delta=\{(2-\delta)\varepsilon N\le L_1\le(2+\delta)\varepsilon N,\ L_2<\delta\varepsilon N\}.$$</div>
<p><em>Proof.</em> Let $T=\lfloor3\varepsilon N\rfloor$ and $W_T=\max_{t\le T}|M_t|$. The deterministic calculation in <a href="/tag/AUTD/">AUTD</a> gives</p>
<div class="math-display">$$\max_{t\le T}\left|Y_t-\varepsilon t+\frac{t^2}{2N}\right|\le(1+12\varepsilon)W_T+15\varepsilon+\frac{45}{2}\varepsilon^3N.$$</div>
<p>For any fixed $\eta>0$, its last two terms are $o(\varepsilon^2N)$. N9DF therefore implies, for suitable positive constants depending on $\eta$,</p>
<div class="math-display">$$\mathbb P\!\left(\max_{t\le T}\left|Y_t-\varepsilon t+\frac{t^2}{2N}\right|>\eta\varepsilon^2N\right)\le C_\eta e^{-c_\eta R}.$$</div>
<p>Take $a=\delta/4$ and $\eta=a/8$. On the complementary event the walk is positive between integer times near $a\varepsilon N$ and $(2-a)\varepsilon N$, and by a time near $(2+a)\varepsilon N$ it is below its minimum before $a\varepsilon N$ by more than one. These claims follow from the parabola $z-z^2/2$, which is positive on $[a,2-a]$, nonnegative before $a$ and negative at $2+a$; the stated margins absorb integer rounding for large $N$. The record-time identity consequently produces one excursion starting before $a\varepsilon N+O(1)$ and ending at a time $\sigma$ between $(2-a)\varepsilon N-O(1)$ and $(2+a)\varepsilon N+O(1)$. Its length is in the required interval for $L_1$, and every earlier component has order less than $\delta\varepsilon N$.</p>
<p>Define $\sigma$ on every outcome as the first empty-queue time at or after $\lceil(2-a)\varepsilon N\rceil$. Conditional on the stopped history, the remaining graph is $G(m,p)$ with $m=N-\sigma$. On the indicated range of $\sigma$, for all large $N$, $m\ge N/2$ and</p>
<div class="math-display">$$d=1-mp\ge\varepsilon/2,\qquad d=O(\varepsilon),\qquad I=-d-\log(1-d)\ge\varepsilon^2/8.$$</div>
<p>Use <a href="/tag/RN5K/">RN5K</a> with $k=\lceil\delta\varepsilon N\rceil$. Since $mp\ge1/2$ and $1-e^{-I}\ge I/2$ eventually, it bounds the conditional probability of a remaining component of order at least $k$ by</p>
<div class="math-display">$$C_\delta N\varepsilon^{-2}(\varepsilon N)^{-5/2}e^{-\delta R/8}=C_\delta R^{-3/2}e^{-\delta R/8}.$$</div>
<p>Integrate this bound on the event that $\sigma$ is in its indicated range, which is measurable at $\sigma$. We have not conditioned the remaining graph on the full good-trajectory event. Add the probability that the trajectory estimate fails. Outside these exceptional events the long excursion is the unique giant and all other components have order below $\delta\varepsilon N$. $\square$</p>

## Moments of the remaining component sizes {#section-er-rank-moments}

<a id="tag-DNIW" data-assertion="theorem" data-title="All fixed positive moments of barely supercritical component sizes converge on their leading scales"></a>
<p>For $G(N,(1+\varepsilon)/N)$ with $\varepsilon\to0$ and $R=N\varepsilon^3\to\infty$, put $b_N=2\varepsilon^{-2}\log R$. For every fixed $q>0$ and every fixed integer $r\ge2$,</p>
<div class="math-display">$$\mathbb E\left|\frac{L_1}{2\varepsilon N}-1\right|^q\longrightarrow0,\qquad \mathbb E\left|\frac{L_r}{b_N}-1\right|^q\longrightarrow0.$$</div>
<p>Consequently $\mathbb E L_1^q\sim(2\varepsilon N)^q$ and $\mathbb E L_r^q\sim b_N^q$. In particular every fixed rank after the giant has mean asymptotic to $2\varepsilon^{-2}\log R$ and variance $o(b_N^2)$.</p>
<p><em>Proof.</em> The probability limits are <a href="/tag/2KT9/">2KT9</a>. By <a href="/tag/PMEN/">PMEN</a>, all positive moments of $L_1/(\varepsilon N)$ are uniformly bounded. Applying the bound with an exponent larger than $q$ makes its $q$th powers uniformly integrable, proving the first conclusion.</p>
<p>For the smaller components fix $\delta=1/8$ and use $E_\delta$ from <a href="/tag/PW6A/">PW6A</a>. Conditional on $E_\delta$ and the vertex set $S$ of its giant, independence of the internal, boundary and complementary edges gives the exact law</p>
<div class="math-display">$$G(m,p)\ \text{conditioned on}\ \{L_1(G(m,p))<\delta\varepsilon N\},\qquad m=N-|S|.$$</div>
<p>Indeed the other requirements specify that $S$ has an allowed size, is connected and has closed boundary. Uniformly over these sizes, $m/N\to1$ and $d_m=1-mp$ satisfies $\varepsilon/2\le d_m\le2\varepsilon$ for all sufficiently large $N$. RN5K shows that the conditioning event has probability at least $1-Ce^{-cR}\ge1/2$. For every integer $k\ge1$, it also gives</p>
<div class="math-display">$$\mathbb P(L_1(G(m,p))\ge k)\le C N\varepsilon^{-2}k^{-5/2}e^{-\varepsilon^2k/8}.$$</div>
<p>Take $k=\lfloor xb_N\rfloor+1$. Divide by the conditioning probability and mix over $S$. For $x\ge8$ and $R\ge e$ this yields</p>
<div class="math-display">$$\mathbb P(L_2/b_N>x,\ E_\delta)\le\frac{CR}{(x\log R)^{5/2}}e^{-x\log R/4}\le Ce^{-x/8}.$$</div>
<p>Thus $(L_2/b_N)\mathbf1_{E_\delta}$ has uniformly bounded moments of every fixed positive order. On the complement, Cauchy–Schwarz, PMEN and PW6A give, for every $q>0$,</p>
<div class="math-display">$$\begin{aligned}\mathbb E\bigl[(L_2/b_N)^q\mathbf1_{E_\delta^c}\bigr]&\le\left(\frac{\varepsilon N}{b_N}\right)^q\bigl[\mathbb E(L_1/(\varepsilon N))^{2q}\bigr]^{1/2}\mathbb P(E_\delta^c)^{1/2}\\&\le C_q\left(\frac R{\log R}\right)^q e^{-cR}\longrightarrow0.\end{aligned}$$</div>
<p>This is the step for which a bound by $N$ alone would be insufficient: no restriction relates the rate of decay of $\varepsilon$ to the growth of $R$. For each fixed $r\ge2$, use $L_r\le L_2$ and the same estimates with an exponent larger than $q$. They give uniform integrability at the logarithmic scale. The probability convergence in 2KT9 now proves convergence in $q$th absolute error; uniform integrability also gives convergence of the raw $q$th moments. Taking $q=1,2$ gives the assertions about means and variances. $\square$</p>
<p>These are leading-scale moment statements. They do not identify the centered moments at the smaller Gaussian scale of <a href="/tag/UKVG/">UKVG</a>, or a centered extreme-value law for the remaining components. The source probability theorem and its conditional-complement argument are discussed in the <a href="/sources/nachmias-peres-outside-window/">Nachmias–Peres source record</a>; the exponential block estimate and moment argument above are supplied here.</p>


## The dual parameter and the extreme-size normalization {#section-er-dual-extreme-normalization}

<p>Return to $G(N,\lambda/N)$ with $\lambda=1+\varepsilon$, $\varepsilon\to0$ and $R=N\varepsilon^3\to\infty$. Let $\rho>0$ solve $1-\rho=e^{-\lambda\rho}$. Define</p>
<div class="math-display">$$I=\lambda-1-\log\lambda=\varepsilon-\log(1+\varepsilon),\qquad B=\log\frac{NI^{3/2}}{\lambda\sqrt{2\pi}},\qquad D=B-\frac52\log B,\qquad s_N(k)=Ik-D.$$</div>
<p>These expressions are used for sufficiently large $N$, when $B>0$. The rate $I$ is positive and is asymptotic to $\varepsilon^2/2$.</p>

<a id="tag-DD9N" data-assertion="proposition" data-title="The exact supercritical extreme normalization is stable under the giant's size fluctuations"></a>
<p>Put $m_*=N(1-\rho)$ and $c_*=\lambda(1-\rho)$. Then $1-c_*\sim\varepsilon$, and</p>
<div class="math-display">$$c_*-1-\log c_*=I,\qquad \log\frac{m_* I^{3/2}}{c_*\sqrt{2\pi}}=B.$$</div>
<p>Let $w_N\to\infty$ satisfy $w_N\log R/\sqrt R\to0$. For every integer $m$ with $|m-m_*|\le w_N\sqrt{N/\varepsilon}$, set</p>
<div class="math-display">$$c_m=\frac{\lambda m}{N},\quad d_m=1-c_m,\quad I_m=c_m-1-\log c_m,\quad B_m=\log\frac{mI_m^{3/2}}{c_m\sqrt{2\pi}},\quad D_m=B_m-\frac52\log B_m.$$</div>
<p>Uniformly over these integers, $d_m/\varepsilon\to1$, $md_m^3/R\to1$, and</p>
<div class="math-display">$$\left|\frac{I_m}{I}-1\right|=O\!\left(\frac{w_N}{\sqrt R}\right),\qquad |B_m-B|+|D_m-D|=O\!\left(\frac{w_N}{\sqrt R}\right),$$</div>
<div class="math-display">$$\sup_m\left|\frac{I_m}{I}(D+x)-D_m-x\right|\longrightarrow0\qquad(x\in\mathbb R\ \text{fixed}).$$</div>
<p><em>Proof.</em> Since $\log c_*=\log\lambda-\lambda\rho$ and $c_*=\lambda-\lambda\rho$, subtraction gives the first identity. Also $m_*/c_*=N/\lambda$, proving the second. The expansion $\rho=2\varepsilon+O(\varepsilon^2)$ from <a href="/tag/MEUA/">MEUA</a> gives $c_*=1-\varepsilon+O(\varepsilon^2)$.</p>
<p>Write $h_N=w_N/\sqrt R=o(1)$. The allowed change in $m$ gives $c_m-c_*=O(\varepsilon h_N)$, so $d_m/\varepsilon\to1$ and $m/N\to1$. On this range the derivative of $c-1-\log c$ is $1-1/c=O(\varepsilon)$. Thus $I_m-I=O(\varepsilon^2h_N)$, giving the relative-rate bound. The exact identity $m/c_m=N/\lambda$ then yields</p>
<div class="math-display">$$B_m-B=\frac32\log(I_m/I)=O(h_N).$$</div>
<p>Now $B=\log R-\log(4\sqrt\pi)+o(1)$ and $D=O(\log R)$. The derivative of $b-\tfrac52\log b$ is bounded near these growing values, giving the bound on $D_m-D$. The final difference is $(I_m/I-1)(D+x)+(D-D_m)$, of order $h_N\log R=o(1)$. $\square$</p>

## Independence of the giant and the smaller extremes {#section-er-joint-extreme-counts}

<p>Select a largest component $C_{\max}$, breaking any ties by a fixed ordering of vertex sets, and exclude it from all counts in this section. Put</p>
<div class="math-display">$$W_N=\frac{L_1-N\rho}{\sqrt{2N/\varepsilon}}.$$</div>

<a id="tag-OH30" data-assertion="theorem" data-title="The Gaussian giant and the Poisson counts of smaller extreme components have independent joint limits"></a>
<p>Fix $x_1<\cdots<x_m$. Let $Z_{N,j}$ count components other than $C_{\max}$ with $s_N(|C|)\in(x_j,x_{j+1}]$ for $j<m$, and let $Z_{N,m}$ count those with $s_N(|C|)>x_m$. Then</p>
<div class="math-display">$$(W_N,Z_{N,1},\ldots,Z_{N,m})\ \xrightarrow{\ d\ }\ (G,P_1,\ldots,P_m),$$</div>
<p>where $G$ is standard normal, the $P_j$ are independent Poisson variables with means $e^{-x_j}-e^{-x_{j+1}}$ and $e^{-x_m}$, and $G$ is independent of the entire count vector. With probability tending to one, every counted component is a tree; the same joint limit therefore holds for the corresponding tree counts outside $C_{\max}$.</p>
<p><em>Proof.</em> By <a href="/tag/UKVG/">UKVG</a>, $W_N$ converges to a standard normal variable. Choose $w_N\to\infty$ as in <a href="/tag/DD9N/">DD9N</a>; such a choice exists because $\log R/\sqrt R\to0$. Tightness gives</p>
<div class="math-display">$$\mathbb P\bigl(|L_1-N\rho|\le w_N\sqrt{N/\varepsilon}\bigr)\longrightarrow1.$$</div>
<p>Intersect this event with $E_\delta$ from <a href="/tag/PW6A/">PW6A</a>, taking $\delta=1/8$, and call the intersection $H_N$. On $H_N$ the giant is unique. Conditional on its vertex set $S$ and on $E_\delta$, the remaining graph has exactly the law</p>
<div class="math-display">$$G(m,\lambda/N)\ \text{conditioned on}\ \{L_1(G(m,\lambda/N))<\delta\varepsilon N\},\qquad m=N-|S|.$$</div>
<p>This is the conditional-complement identity used in <a href="/tag/DNIW/">DNIW</a>. For every allowed $m$, the conditioning event has probability $1-O(e^{-cR})$ uniformly, by <a href="/tag/RN5K/">RN5K</a>. Conditioning changes the probability of any event by $o(1)$ uniformly. Given $S$, the extra size restriction defining $H_N$ is deterministic and imposes no further condition on the complementary edges.</p>
<p>Write the unconditioned complementary law as $G(m,(1-d_m)/m)$. DD9N gives $d_m\to0$ and $md_m^3\to\infty$ uniformly. Apply the subcritical joint count theorem <a href="/tag/7W39/">7W39</a> with its own normalization $I_mk-D_m$. A threshold $x$ in our normalization corresponds to</p>
<div class="math-display">$$I_mk-D_m>\frac{I_m}{I}(D+x)-D_m,$$</div>
<p>whose right-hand side tends uniformly to $x$. Moving the thresholds in this way preserves the count limit: bracket each by $x-\eta$ and $x+\eta$, use the joint interval-count theorem, and then let $\eta\downarrow0$. The limiting Poisson intensity gives vanishing probability of a point in the shrinking intervals. The same reasoning and the tree assertion of 7W39 exclude cyclic components above the lowest threshold.</p>
<p>All these conclusions hold uniformly over the allowed integer $m$. Otherwise a sequence of violating choices would still satisfy $d_m\to0$, $md_m^3\to\infty$ and the threshold estimates, contradicting the subcritical theorem. In particular, for each fixed vector $z$ of nonnegative integers, the conditional probability of $Z_N=z$ given $S$ and $H_N$ is $\pi(z)+o(1)$ uniformly, where $\pi$ is the product Poisson law in the statement. Since $W_N$ is determined by $|S|$,</p>
<div class="math-display">$$\mathbb P(W_N\le t,\ Z_N=z,\ H_N)=\bigl(\pi(z)+o(1)\bigr)\mathbb P(W_N\le t,\ H_N).$$</div>
<p>The error is uniform before mixing over $S$. Now $\mathbb P(H_N)\to1$ and $W_N\Rightarrow G$, so the last expression tends to $\pi(z)\Phi(t)$. These identities for all $t$ and $z$ give the stated joint limit and independence. The uniform tree assertion transfers in the same mixture. $\square$</p>

## The joint ordered-size law above the window {#section-er-joint-ordered-extremes}

<a id="tag-K1HI" data-assertion="corollary" data-title="The Gaussian giant is asymptotically independent of the full fixed-rank extreme-size vector outside it"></a>
<p>In the preceding regime, for every fixed $K\ge1$,</p>
<div class="math-display">$$\left(W_N,s_N(L_2),\ldots,s_N(L_{K+1})\right)\ \xrightarrow{\ d\ }\ \left(G,-\log E_1,-\log(E_1+E_2),\ldots,-\log(E_1+\cdots+E_K)\right),$$</div>
<p>where $G$ is standard normal and $E_1,E_2,\ldots$ are independent mean-one exponential variables, independent of $G$. The ordered extreme sizes share these partial sums; they are not mutually independent. With probability tending to one, the components of ranks $2,\ldots,K+1$ are trees. Consequently the same limit holds when $L_{j+1}$ is replaced by the $j$th largest tree-component size outside $C_{\max}$, with zero padding.</p>
<p>For each fixed $r\ge2$, the marginal formula is</p>
<div class="math-display">$$\mathbb P(s_N(L_r)\le x)\longrightarrow e^{-e^{-x}}\sum_{j=0}^{r-2}\frac{e^{-jx}}{j!}.$$</div>
<p><em>Proof.</em> For large $N$, the event $s_N(L_{j+1})\le a_j$ is equivalent to having at most $j-1$ components outside $C_{\max}$ above $a_j$. Apply <a href="/tag/OH30/">OH30</a> to the distinct thresholds among $a_1,\ldots,a_K$, together with the event $W_N\le t$. As in 7W39, the limiting counts are the counts of the points $-\log(E_1+\cdots+E_j)$. Their continuous marginals give convergence of the ordered vector, and the factorization in OH30 gives independence from $G$. At a fixed sufficiently low threshold, all exceedances are trees with probability tending to one. The limiting $K$th point lies above this threshold with probability tending to one as the threshold tends to $-\infty$, proving the tree assertion. The single-threshold count is Poisson with mean $e^{-x}$, which gives the displayed marginal formula. $\square$</p>

## The bias from replacing the exact rate {#section-er-extreme-rate-bias}

<a id="tag-KU4Y" data-assertion="corollary" data-title="Quadratic-rate centering of supercritical non-giant extremes has a two-thirds epsilon-log-R bias"></a>
<p>For a fixed rank $r\ge2$, put</p>
<div class="math-display">$$H_{N,r}=\frac{\varepsilon^2}{2}L_r-\log R+\frac52\log\log R+\log(4\sqrt\pi).$$</div>
<p>If $\varepsilon\log R\to a\in[0,\infty)$, then</p>
<div class="math-display">$$(W_N,H_{N,r})\ \xrightarrow{\ d\ }\ \left(G,G_{r-1}+\frac23a\right),$$</div>
<p>with the independent variables defined above. If $\varepsilon\log R\to\infty$, then $H_{N,r}\to+\infty$ in probability. Thus the quadratic rate gives the unshifted extreme-size limit when $\varepsilon\log R\to0$.</p>
<p><em>Proof.</em> Taylor expansion gives</p>
<div class="math-display">$$I=\frac{\varepsilon^2}{2}-\frac{\varepsilon^3}{3}+O(\varepsilon^4),\qquad \frac{\varepsilon^2}{2I}-1=\frac23\varepsilon+O(\varepsilon^2),$$</div>
<div class="math-display">$$D=\log R-\frac52\log\log R-\log(4\sqrt\pi)+o(1).$$</div>
<p>Since $s_N(L_r)=O_{\mathbb P}(1)$ by K1HI and $IL_r=D+s_N(L_r)$, substitution yields</p>
<div class="math-display">$$H_{N,r}=s_N(L_r)+\frac23\varepsilon\log R\,(1+o(1))+o_{\mathbb P}(1).$$</div>
<p>The joint limit in K1HI proves the finite-shift case; its tightness proves divergence when the deterministic shift diverges. $\square$</p>
<p>The joint statements concern the barely supercritical complete graph outside the critical window. They do not assert convergence of centered moments, or a joint critical-window law. The proof combines the written Gaussian theorem with the exact conditional-complement law and the multivariate tree-count argument; no new source erratum is involved.</p>


## Exponential tails before the giant starts {#section-er-early-exponential-tails}

<p>The distributional limits above can be strengthened to convergence of moments at their centered scales. Throughout the next four sections, $p=(1+\varepsilon)/N$, $\varepsilon\to0$ and $R=N\varepsilon^3\to\infty$. Keep the exploration variables $S_t,Z_t,C_t$ from <a href="/tag/UEXT/">UEXT</a>, and let $t_1=\lfloor\varepsilon N\rfloor$ and $\tau=\max\{t\le t_1:A_t=0\}$.</p>

<a id="tag-Y85E" data-assertion="proposition" data-title="The number and total duration of exploration components before the giant have exponential tails on their natural scales"></a>
<p>There are absolute constants $c,C>0$ such that, for all sufficiently large $N$ and every $u\ge1$,</p>
<div class="math-display">$$\mathbb P(\varepsilon C_{t_1}>u)+\mathbb P(\varepsilon^2\tau>u)\le Ce^{-cu}.$$</div>
<p>Consequently both variables have uniformly bounded moments of every fixed positive order.</p>
<p><em>Proof.</em> Write $\Delta_i=\eta_i-\mathbb E(\eta_i\mid\mathcal F_{i-1})$ and $r=1-p$. Up to time $T=\lfloor3\varepsilon N\rfloor$ the deterministic weights $r^{-i}$ are at most $2$ eventually. The centered-binomial calculation in <a href="/tag/N9DF/">N9DF</a> therefore gives</p>
<div class="math-display">$$\mathbb E\!\left(e^{\theta r^{-i}\Delta_i}\mid\mathcal F_{i-1}\right)\le e^{8\theta^2}\qquad(|\theta|\le1/2).$$</div>
<p>Stopping the exponential supermartingale at its first crossing, and choosing $\theta=\min\{v/(16h),1/4\}$, gives, for deterministic integers $s\ge0$, $h\ge1$ with $s+h\le T$ and every $v>0$,</p>
<div class="math-display">$$\mathbb P\!\left(\max_{0\le j\le h}|S_{s+j}-S_s|\ge v\,\middle|\,\mathcal F_s\right)\le2\exp\!\left[-\frac1{32}\min\left\{\frac{v^2}{h},v\right\}\right].$$</div>
<p>The argument applies separately to each sign. All stopping times are bounded.</p>
<p>UEXT's deterministic reflection bound says, with a fixed $c_0>0$,</p>
<div class="math-display">$$(1-pt_1)C_{t_1}\le1+\max_{s\le t_1}(-c_0\varepsilon s-S_s)_+.$$</div>
<p>To bound the maximum by $u/\varepsilon$, first consider $s\le u\varepsilon^{-2}$, then the intervals $2^ju\varepsilon^{-2}\le s\le2^{j+1}u\varepsilon^{-2}$, truncating every interval at $t_1$. The first crossing requires $\max|S_s|\ge u/\varepsilon$; a crossing in the $j$th later interval requires $\max_{s\le2^{j+1}u\varepsilon^{-2}}|S_s|\ge c_0 2^ju/\varepsilon$. The maximal bound gives probabilities at most $Ce^{-cu}$ and $Ce^{-c2^ju}$, respectively. Floors and ceilings change only the constants. Summation gives $Ce^{-cu}$. Since $pt_1\to0$, rescaling $u$ and enlarging $C$ on a bounded interval proves the assertion for $\varepsilon C_{t_1}$.</p>
<p>At a time $s\le t_1$ with $A_s=0$, the exact identity $A_s=x_s+r^sS_s+E_s$, with $E_s\ge0$ and $x_s/r^s\ge c_0\varepsilon s$, implies $S_s\le-c_0\varepsilon s$. A zero after $u\varepsilon^{-2}$ is therefore covered by the same dyadic intervals and the same summable bounds. This proves the assertion for $\tau$. Integrating either exponential tail gives all the stated moment bounds. $\square$</p>

## Centered moments of the giant {#section-er-centered-giant-moments}

<a id="tag-LXGK" data-assertion="theorem" data-title="The centered barely supercritical giant converges in all polynomial moments at its Gaussian scale"></a>
<p>Let $\rho>0$ solve $1-\rho=e^{-(1+\varepsilon)\rho}$ and put $W_N=(L_1-N\rho)/\sqrt{2N/\varepsilon}$. For every real $q>0$,</p>
<div class="math-display">$$\mathbb E|W_N|^q\longrightarrow\mathbb E|G|^q,\qquad G\sim\mathcal N(0,1).$$</div>
<p>All signed integer moments converge as well. In particular,</p>
<div class="math-display">$$\mathbb E L_1=N\rho+o\!\left(\sqrt{N/\varepsilon}\right),\qquad \operatorname{Var}(L_1)\sim\frac{2N}{\varepsilon}.$$</div>
<p><em>Proof.</em> We first obtain uniform moment bounds for $W_N$. Use the good-trajectory event and the stopped-remainder estimate in the proof of <a href="/tag/PW6A/">PW6A</a>, with $\delta=1/8$. Except on an event of probability at most $Ce^{-cR}$, the component explored at $t_1$ is the unique giant, its completion time $\sigma$ lies in $[7\varepsilon N/4,9\varepsilon N/4]$, and</p>
<div class="math-display">$$L_1=\sigma-\tau,\qquad C_\sigma=C_{t_1}.$$</div>
<p>Call this event $F_N$. The exponential estimate concerns the trajectory as well as the final sizes: PW6A constructs the long excursion first and then excludes a large component in the stopped remainder. No conditioning on the whole trajectory is used to declare that remainder independent.</p>
<p>Let $t_*$ be the positive real zero of $x_t=N-t-N(1-p)^t$. The calculations in <a href="/tag/UKVG/">UKVG</a> give $t_*-N\rho=O(1)$ and $-x'(t)\asymp\varepsilon$ on the displayed interval. Both $t_*$ and $\sigma$ lie there eventually on $F_N$. At $\sigma$,</p>
<div class="math-display">$$0=x_\sigma+Z_\sigma+E_\sigma,\qquad 0\le E_\sigma\le C_{t_1}.$$</div>
<p>The mean value theorem consequently gives the pathwise bound</p>
<div class="math-display">$$|W_N|\mathbf1_{F_N}\le C\left(\frac{\max_{t\le T}|S_t|}{\sqrt{\varepsilon N}}+
\frac{\varepsilon C_{t_1}+\varepsilon^2\tau}{\sqrt R}+
\sqrt{\frac{\varepsilon}{N}}\right),\qquad T=\lfloor3\varepsilon N\rfloor.$$</div>
<p>Here $|Z_t|\le|S_t|$. The weighted maximal estimate in <a href="/tag/Y85E/">Y85E</a> shows that $\max_{t\le T}|S_t|/\sqrt{\varepsilon N}$ has bounded moments of every fixed order: its tail at $v\ge1$ is at most $C\exp[-c\min\{v^2,v\sqrt{\varepsilon N}\}]\le Ce^{-cv}$. Y85E supplies the same moment bounds for the two early-exploration errors.</p>
<p>On the exceptional event, use $\rho=O(\varepsilon)$ and the global bound <a href="/tag/PMEN/">PMEN</a>. For each $q>0$, Cauchy–Schwarz gives</p>
<div class="math-display">$$\mathbb E\bigl[|W_N|^q\mathbf1_{F_N^c}\bigr]
\le C_q R^{q/2}\left[\mathbb E\left(1+\frac{L_1}{\varepsilon N}\right)^{2q}\right]^{1/2}\mathbb P(F_N^c)^{1/2}
\le C_q R^{q/2}e^{-cR}\longrightarrow0.$$</div>
<p>Thus all positive moments of $W_N$ are uniformly bounded. Applying this with an exponent larger than $q$ gives uniform integrability of $|W_N|^q$. The Gaussian convergence in UKVG now yields the absolute and signed moment limits. The first two moments give the expectation and variance assertions. $\square$</p>

## Joint centered moments of the smaller extremes {#section-er-joint-centered-moments}

<p>Keep the exact normalization from <a href="/tag/DD9N/">DD9N</a>:</p>
<div class="math-display">$$I=\varepsilon-\log(1+\varepsilon),\qquad B=\log\frac{NI^{3/2}}{(1+\varepsilon)\sqrt{2\pi}},\qquad D=B-\frac52\log B,\qquad Y_{N,j}=IL_{j+1}-D.$$</div>
<p>For $j\ge1$, let $G_j=-\log(E_1+\cdots+E_j)$, where the $E_i$ are independent mean-one exponentials; let $G$ be standard normal and independent of this sequence. The extreme coordinates $G_j$ remain correlated with each other.</p>

<a id="tag-NVPH" data-assertion="theorem" data-title="The Gaussian giant and each fixed vector of smaller centered extreme sizes converge jointly in all polynomial moments"></a>
<p>For every fixed $K\ge1$ and every continuous $f:\mathbb R^{K+1}\to\mathbb R$ satisfying $|f(z)|\le C(1+\|z\|^q)$ for some finite $C,q>0$,</p>
<div class="math-display">$$\mathbb E f(W_N,Y_{N,1},\ldots,Y_{N,K})\longrightarrow\mathbb E f(G,G_1,\ldots,G_K).$$</div>
<p>The same conclusion holds when $L_{j+1}$ is replaced by the $j$th largest tree-component size outside a selected largest component, with deterministic tie breaking and zero padding. In particular, for nonnegative integers $a_0,\ldots,a_K$,</p>
<div class="math-display">$$\mathbb E\!\left[W_N^{a_0}\prod_{j=1}^K Y_{N,j}^{a_j}\right]\longrightarrow\mathbb E G^{a_0}\;\mathbb E\prod_{j=1}^K G_j^{a_j}.$$</div>
<p>For each fixed rank $r\ge2$, this also gives</p>
<div class="math-display">$$\mathbb E L_r=\frac{D+\gamma-H_{r-2}+o(1)}{I},\qquad H_0=0,\quad H_k=\sum_{\ell=1}^k\frac1\ell.$$</div>
<p><em>Proof.</em> Fix $\delta=1/8$ and use $E_\delta$ from <a href="/tag/PW6A/">PW6A</a>. Conditional on $E_\delta$ and its giant vertex set $S$, the complementary graph is $G(m,p)$ conditioned on its largest component having size less than $\delta\varepsilon N$, where $m=N-|S|$. This is the exact conditional law in <a href="/tag/DNIW/">DNIW</a>. The conditioning probability is at least $1/2$ uniformly over the allowed $m$, for all large $N$.</p>
<p>Set $c_m=mp$, $d_m=1-c_m$, and define $I_m,B_m,D_m$ as in DD9N. Uniformly on $E_\delta$, $\varepsilon/2\le d_m\le2\varepsilon$ and $m/N\to1$. The subcritical centered-tail bound <a href="/tag/XHEC/">XHEC</a> therefore gives bounded moments of every fixed order for</p>
<div class="math-display">$$V_{m,j}=I_m L_j(G(m,p))-D_m,$$</div>
<p>uniformly over these complementary orders. The estimates in that proof are uniform as $d_m\to0$ and $md_m^3\to\infty$; alternatively, a sequence of violating choices of $m$ would contradict the same bound along that sequence. Conditioning multiplies each nonnegative expectation by at most two. The argument applies to the centered tree ranks too.</p>
<p>It remains to control the random change of normalization in moments. Put $m_*=N(1-\rho)$, $a_m=I_m/I$ and $b_m=a_mD-D_m$. On the whole event $E_\delta$, both $a_m$ and $a_m^{-1}$ are bounded. The rate derivative $1-1/c=O(\varepsilon)$ throughout the interval between $c_m$ and $c_*=(1+\varepsilon)(1-\rho)$ gives</p>
<div class="math-display">$$|a_m-1|\le C\frac{|W_N|}{\sqrt R},\qquad \frac{|m-m_*|}{\varepsilon N}=\frac{\sqrt2\,|W_N|}{\sqrt R}.$$</div>
<p>The exact cancellation $m/c_m=N/(1+\varepsilon)$ gives $B_m-B=\tfrac32\log a_m$. Since $B\asymp\log R$ and $a_m$ stays in a fixed compact subinterval of $(0,\infty)$,</p>
<div class="math-display">$$|D_m-D|\le C|a_m-1|,\qquad |b_m|\le C\frac{\log R}{\sqrt R}|W_N|.$$</div>
<p>No restriction to a slowly growing interval for $W_N$ is made here. By <a href="/tag/LXGK/">LXGK</a>, the last bound tends to zero in every fixed positive moment. On $E_\delta$ the rank identity is exact:</p>
<div class="math-display">$$Y_{N,j}=a_m^{-1}(V_{m,j}-b_m).$$</div>
<p>Condition on $S$, use the uniform conditional moments of $V_{m,j}$, and then average. This proves bounded moments of $Y_{N,j}\mathbf1_{E_\delta}$ of every fixed positive order. The proof is unchanged for the tree ranks outside the giant.</p>
<p>On $E_\delta^c$, every such size is between $0$ and $L_1$, so its absolute centered value is at most $C(RL_1/(\varepsilon N)+\log R)$. For each $q>0$, PMEN and PW6A consequently give</p>
<div class="math-display">$$\mathbb E\bigl[|Y_{N,j}|^q\mathbf1_{E_\delta^c}\bigr]\le C_q\bigl(R^q+(\log R)^q\bigr)e^{-cR}\longrightarrow0,$$</div>
<p>and the same estimate holds for the tree ranks. Together with LXGK, these estimates give bounded moments of all orders for each coordinate of the vector. An exponent larger than $q$, and the inequality bounding a finite-dimensional norm by the sum of the coordinate magnitudes, give uniform integrability for every $f$ in the statement. Truncate outside a large ball and apply the joint distributional convergence <a href="/tag/K1HI/">K1HI</a>. This proves the expectation limit, including for the tree vector. The factorization of the mixed moments follows from independence of $G$ and the whole extreme vector. Finally $\mathbb E G_j=\gamma-H_{j-1}$ by <a href="/tag/OL4S/">OL4S</a>; taking expectations in $Y_{N,r-1}=IL_r-D$ proves the expansion. $\square$</p>
<p>The $o(1)$ remains inside the numerator, so the expectation error is $o(I^{-1})$. These polynomial-moment estimates do not assert convergence of exponential transforms throughout the subcritical range $|\alpha|<1$.</p>

## Covariances of the extreme ranks {#section-er-extreme-covariances}

<a id="tag-M7A4" data-assertion="corollary" data-title="The extreme-rank covariance is determined by the larger rank while the Gaussian giant has vanishing scaled covariance with each smaller rank"></a>
<p>For fixed integers $r,s\ge2$,</p>
<div class="math-display">$$I^2\operatorname{Cov}(L_r,L_s)\longrightarrow
\sum_{\ell=\max\{r,s\}-1}^{\infty}\frac1{\ell^2},\qquad
\frac{I}{\sqrt{2N/\varepsilon}}\operatorname{Cov}(L_1,L_r)\longrightarrow0.$$</div>
<p>In particular, $\operatorname{Var}(L_r)\sim I^{-2}\sum_{\ell=r-1}^{\infty}\ell^{-2}$. The first formula also holds for the corresponding tree ranks outside the largest component.</p>
<p><em>Proof.</em> NVPH reduces the assertions to the limiting covariances. Write $S_j=E_1+\cdots+E_j$. For $i<j$, the independent variables $S_i$ and $S_j-S_i$ have gamma densities with parameters $i$ and $j-i$. The change of variables $(S_i,S_j-S_i)=(uv,(1-u)v)$, whose Jacobian is $v$, factors their joint density into a beta density in $u$ and the gamma density of $v=S_j$. Thus $S_i/S_j$ is independent of $S_j$, and</p>
<div class="math-display">$$\operatorname{Cov}(-\log S_i,-\log S_j)=\operatorname{Var}(\log S_j).$$</div>
<p>The gamma integral gives $\mathbb E S_j^t=\Gamma(j+t)/\Gamma(j)$ for $t>-j$. Differentiating its logarithm twice at zero gives $\operatorname{Var}(\log S_j)$. From $\Gamma(j+t)=\Gamma(1+t)\prod_{\ell=1}^{j-1}(\ell+t)$ and Euler's product</p>
<div class="math-display">$$\Gamma(1+t)=e^{-\gamma t}\prod_{\ell=1}^{\infty}(1+t/\ell)^{-1}e^{t/\ell},$$</div>
<p>we obtain $\operatorname{Var}(\log S_j)=\sum_{\ell=j}^{\infty}\ell^{-2}$. The twice-differentiated logarithmic series converges uniformly for $|t|\le1/2$, justifying this calculation. The same formula covers $i=j$, and symmetry covers $i>j$. Substitute $i=r-1$, $j=s-1$. Independence of the Gaussian variable makes its covariance with every extreme coordinate zero. $\square$</p>
<p>This completes the centered polynomial-moment consequences of the outside-window joint law. All results in these sections are for the barely supercritical complete graph; a joint critical-window theorem and near-critical geometric hosts require separate arguments. No published-source correction or formal proof status is asserted here.</p>


## Short disjoint paths in the hypercube {#section-hypercube-short-paths}

<p>We now turn to the Hamming cube $Q_m=\{0,1\}^m$, with $N=2^m$ vertices and graph distance equal to Hamming distance. A coarse path count is enough to join mesoscopic clusters when the supercritical displacement is not too small. Its losses are explicit, so the range of the resulting percolation theorem can be checked directly.</p>

<a id="tag-YI8S" data-assertion="proposition" data-title="Two large vertex sets in the hypercube admit an explicit packing of short vertex-disjoint paths"></a>
<p>Let $m\ge1$, $0<a\le1/2$, and let $A,B\subseteq Q_m$ be disjoint sets with $|A|,|B|\ge aN$. For every integer</p>
<div class="math-display">$$\ell\ge\left\lceil\sqrt{2m\log(2/a)}\right\rceil,$$</div>
<p>there are at least</p>
<div class="math-display">$$K=\left\lfloor\frac{aN}{2(\ell+1)(m+1)^\ell}\right\rfloor$$</div>
<p>pairwise vertex-disjoint $A$–$B$ paths, each of length at most $\ell$. A zero lower bound is permitted.</p>
<p><em>Proof.</em> First take a nonempty set $D\subseteq Q_m$, a uniform vertex $X$, and $f(X)=d(X,D)$. Exposing the independent coordinates of $X$ gives a Doob martingale for $f$. At each step its two possible increments are $\pm b/2$ with $|b|\le1$, since changing one coordinate changes $f$ by at most one. Consequently its conditional exponential moment is at most $\cosh(\theta/2)\le e^{\theta^2/8}$. Multiplication and Chernoff's bound give</p>
<div class="math-display">$$\mathbb P(f-\mathbb Ef\ge t),\ \mathbb P(f-\mathbb Ef\le-t)\le e^{-2t^2/m}\qquad(t\ge0).$$</div>
<p>If $|D|/N=d$, then $\mathbb P(f=0)=d$ implies $\mathbb Ef\le\sqrt{(m/2)\log(1/d)}$. Thus whenever $|D|\ge aN/2$ and $|B|\ge aN$,</p>
<div class="math-display">$$d(D,B)\le\sqrt{2m\log(2/a)}.$$</div>
<p>Indeed, otherwise every vertex of $B$ would have distance greater than $\mathbb Ef+\sqrt{(m/2)\log(2/a)}$ from $D$, whereas the upper-tail bound assigns that event probability at most $a/2$.</p>
<p>Choose the paths successively. After $j<K$ choices let $U$ be their vertices, so $|U|\le j(\ell+1)$. A radius-$\ell$ ball has at most $(m+1)^\ell$ vertices: every vertex in it can be reached by $\ell$ moves, each either a coordinate flip or a stay. Therefore the $\ell$-neighbourhood of $U$ contains fewer than $aN/2$ vertices. The set $D=A\setminus\{x:d(x,U)\le\ell\}$ has size at least $aN/2$. The preceding distance bound supplies a path of length at most $\ell$ from $D$ to $B$. This path cannot meet $U$, since its initial vertex is farther than $\ell$ from $U$. It is the next path in the packing. Continue until $K$ paths have been chosen. $\square$</p>

## Sprinkling between unions of cube clusters {#section-hypercube-sprinkling-bound}

<a id="tag-5IGY" data-assertion="proposition" data-title="An explicit conditional sprinkling bound joins almost all mass in selected hypercube components"></a>
<p>Fix an arbitrary first-round subgraph of $Q_m$ and select $n$ of its distinct components, with union $U$ of size $M$. Let $0<a\le1/3$ satisfy $M\ge3aN$, and let $\ell,K$ be as in YI8S. Independently sprinkle every cube edge with probability $q\in(0,1]$. Then</p>
<div class="math-display">$$\mathbb P\bigl(\text{no final component contains more than }M-aN
\text{ vertices of }U\mid\text{first round}\bigr)
\le\min\{1,\exp(n\log2-Kq^\ell)\}.$$</div>
<p><em>Proof.</em> If every final component meets $U$ in at most $M-aN$ vertices, there is a union of final components meeting $U$ in a set of size between $aN$ and $M-aN$. To see this, choose a single component if its intersection size lies in that interval. If none does, all nonempty intersection sizes are less than $aN$; accumulate them until their sum first reaches $aN$. That sum is less than $2aN\le M-aN$.</p>
<p>The resulting partition $U=A\mathbin{\dot\cup}B$ has $|A|,|B|\ge aN$. Both parts are unions of selected first-round components, so at most $2^n$ partitions need to be considered. For each fixed partition, choose the $K$ vertex-disjoint paths in YI8S before exposing any sprinkling. A path of length at most $\ell$ is entirely sprinkled open with probability at least $q^\ell$, and these events are independent because the paths are edge-disjoint. Such a path connects the two sides in the final graph, even if its interior lies outside $U$. The chance that all $K$ paths fail is at most $(1-q^\ell)^K\le e^{-Kq^\ell}$. A union bound proves the assertion; when $K=0$ the probability bound is simply one. $\square$</p>

## A giant in a broad supercritical cube regime {#section-hypercube-broad-giant}

<p>Fix $0<\lambda\le1/10$ and define $p_c=p_\lambda$ by $\chi(p_c)=\lambda N^{1/3}$, as in <a href="/tag/EFAQ/">EFAQ</a>. Here the displacement is additive and degree-normalized: $p=p_c+\varepsilon/m$.</p>

<a id="tag-12DQ" data-assertion="theorem" data-title="The hypercube giant has size two epsilon times the volume when log inverse epsilon is little-oh of the cube-root dimension"></a>
<p>Suppose $m\to\infty$, $\varepsilon=\varepsilon_m>0$, $\varepsilon\to0$ and</p>
<div class="math-display">$$\log(1/\varepsilon)=o(m^{1/3}).$$</div>
<p>For independent bond percolation on $Q_m$ at $p=p_c+\varepsilon/m$, the largest component satisfies</p>
<div class="math-display">$$\frac{L_1}{2\varepsilon N}\longrightarrow1\qquad\text{in probability}.$$</div>
<p>This includes every sequence $\varepsilon\ge m^{-2}$ tending to zero, and also $\varepsilon=\exp(-m^\alpha)$ for each fixed $0<\alpha<1/3$.</p>
<p><em>Proof.</em> The strong triangle estimate <a href="/tag/87Y4/">87Y4</a> has the form $\eta(u)\le a_m+4\chi(u)^3/N$ for $u\le p_c$, with $a_m\to0$. At $p_c$ its bound is eventually less than $1/100$, because $4\lambda^3<1/100$. EFAQ gives $mp_c\to1$. Thus the hypotheses of the large-cluster mass estimate <a href="/tag/7Y5K/">7Y5K</a> hold. Our displacement condition implies $\varepsilon^bN^c\to\infty$ for every fixed $b,c>0$. In particular, both $\varepsilon^3N$ and $\varepsilon^5N$ diverge.</p>
<p>For these parameters the cutoff in 7Y5K is eventually</p>
<div class="math-display">$$k=\varepsilon^{-2}(\varepsilon^3N)^{1/6}=\varepsilon^{-3/2}N^{1/6},\qquad
\mathbb E\left(\frac{Z_k}{2\varepsilon N}-1\right)^2\longrightarrow0.$$</div>
<p>Indeed $(\varepsilon^5N)^{1/4}/(\varepsilon^3N)^{1/6}=\varepsilon^{3/4}N^{1/12}\to\infty$. The same statement applies after multiplying $\varepsilon$ by any fixed positive constant. At the final parameter it already gives $L_1\le(2+o_{\mathbb P}(1))\varepsilon N$.</p>
<p>For the lower bound fix $0<\theta<1/10$, set $\varepsilon_1=(1-\theta)\varepsilon$, and take</p>
<div class="math-display">$$p_1=p_c+\frac{\varepsilon_1}{m},\qquad
q=\frac{p-p_1}{1-p_1}\ge\frac{\theta\varepsilon}{m}.$$</div>
<p>An independent $p_1$ first round followed by $q$ sprinkling has exactly parameter $p$. Select all first-round components of size at least $k_1=\varepsilon_1^{-3/2}N^{1/6}$. With probability tending to one their total mass $M$ satisfies</p>
<div class="math-display">$$2(1-2\theta)\varepsilon N\le M\le3\varepsilon N,\qquad
n\le M/k_1\le3N^{5/6}.$$</div>
<p>Work conditionally on such a first round. Put $a=\theta\varepsilon$ and $\ell=\lceil\sqrt{2m\log(2/a)}\rceil$. Then $M\ge3aN$. Writing $b=\log(1/\varepsilon)$, we have</p>
<div class="math-display">$$\ell=O_\theta(\sqrt{m(1+b)}),\qquad
\ell\log\frac{m+1}{q}=O_\theta\!\left(\sqrt{m(1+b)}(\log m+b)\right)=o(m).$$</div>
<p>Also $\log(1/a)+\log(\ell+1)=o(m)$. The unfloored packing bound tends to infinity exponentially in $m$, so its floor is at least half that bound eventually. Hence</p>
<div class="math-display">$$Kq^\ell\ge\frac{aN}{4(\ell+1)}
\left(\frac q{m+1}\right)^\ell=N^{1-o(1)}.$$</div>
<p>This dominates $n\log2\le3(\log2)N^{5/6}$. By <a href="/tag/5IGY/">5IGY</a>, the conditional probability of failure tends to zero, uniformly over the first rounds under consideration. Thus some final component has size greater than $M-aN\ge(2-5\theta)\varepsilon N$ with probability tending to one. Letting the fixed $\theta$ tend to zero proves the lower bound and the theorem. $\square$</p>

## Susceptibility and the mass outside the cube giant {#section-hypercube-giant-moments}

<a id="tag-E6FX" data-assertion="corollary" data-title="In the broad supercritical cube regime the giant converges in mean square and the remaining squared component mass is negligible"></a>
<p>Under the hypotheses of 12DQ, with component sizes $L_1\ge L_2\ge\cdots$,</p>
<div class="math-display">$$\mathbb E\left(\frac{L_1}{2\varepsilon N}-1\right)^2\longrightarrow0,\qquad
\frac{\chi(p)}{4\varepsilon^2N}\longrightarrow1,\qquad
\frac{\mathbb E\sum_{j\ge2}L_j^2}{\varepsilon^2N^2}\longrightarrow0.$$</div>
<p>In particular $L_2/(\varepsilon N)\to0$ in mean square and in probability, $\mathbb E L_1\sim2\varepsilon N$, and $\operatorname{Var}(L_1)=o(\varepsilon^2N^2)$.</p>
<p><em>Proof.</em> At the final parameter use the cutoff $k=\varepsilon^{-3/2}N^{1/6}$ and write $Z=Z_k$. By 7Y5K, $Z/(2\varepsilon N)\to1$ in mean square, while $k/(\varepsilon N)=\varepsilon^{-5/2}N^{-5/6}\to0$. Deterministically $L_1\le Z+k$. Thus $\limsup\mathbb E[(L_1/(2\varepsilon N))^2]\le1$. The probability convergence in 12DQ supplies the matching lower bound for the first and second moments; the first-moment upper bound follows by Cauchy–Schwarz. Expanding the square proves the first conclusion.</p>
<p>For every configuration,</p>
<div class="math-display">$$L_1^2\le\sum_{j\ge1}L_j^2\le Z^2+kN.$$</div>
<p>The components below the cutoff contribute at most $k$ times their total volume; the squares of the larger sizes sum to at most the square of their total volume. Transitivity gives $\chi(p)=N^{-1}\mathbb E\sum_j L_j^2$. Since $k/(\varepsilon^2N)=\varepsilon^{-7/2}N^{-5/6}\to0$, both outer expectations are asymptotic to $4\varepsilon^2N^2$. This proves the susceptibility limit. Subtract $\mathbb E L_1^2$ to obtain the third assertion, which also bounds $\mathbb E L_2^2$. $\square$</p>
<p>The hypothesis $\log(1/\varepsilon)=o(m^{1/3})$ ensures that the losses in the path count are subexponential in $m$. These arguments do not settle the full range $\varepsilon^3N\to\infty$. The narrower near-window range, and corresponding torus results, remain separate. The comparison is van der Hofstad–Nachmias, Section 7.2; the explicit packing above uses a separate concentration argument with deliberately coarse losses.</p>


## Exploration at the critical scale {#section-er-critical-exploration}

<p>At $p=(1+\lambda_NN^{-1/3})/N$, with $\lambda_N\to\lambda\in\mathbb R$, the <a href="/tag/CY46/">critical-window exploration theorem</a> gives the joint Brownian limit of the walk, active queue and root count on the $N^{2/3}$ time scale. The limiting walk is $B(t)+\lambda t-t^2/2$, with reflection at its running minimum. <a href="/tag/GGL3/">Surplus-edge marks</a> converge jointly to a Poisson point measure whose conditional intensity is the reflected queue. This covers both signs of $\lambda$ and differs from the deterministic trajectory and Gaussian giant outside the window. The ranked critical component law still requires an excursion and late-component argument.</p>


## The ranked law inside the window {#section-er-critical-ranked-law}

<p>The <a href="/tag/M7BY/">critical ranked-component theorem</a> now completes the excursion step left open above: for $p_N=(1+\lambda_NN^{-1/3})/N$ with $\lambda_N\to\lambda$, all sizes scaled by $N^{-2/3}$ converge in $\ell^2$, jointly with every fixed vector of ranked surplus counts. The limit consists of the ordered excursion lengths of reflected Brownian motion with parabolic drift and conditionally independent Poisson counts with excursion-area means. A stopped unexplored-graph estimate controls the squared mass of late components. This is a fixed-window-parameter law; the multiplicative-coalescent evolution in the parameter remains separate.</p>



## Coupling the critical parameters {#section-er-critical-parameter-laws}

<p>The <a href="/tag/Z8T1/">finite-parameter critical law</a> now couples the ranked component sizes at any finite list of window parameters. Under the usual common-uniform-edge coupling, the limit evolves by the multiplicative-coalescent kernels on $\ell^2_\downarrow$. The proof includes their <a href="/tag/7HLE/">joint continuity in time and initial masses</a>. Convergence in a path-space topology and the joint evolution of surplus counts remain separate.</p>



## The whole critical size path {#section-er-critical-path-law}

<p>The <a href="/tag/TIGK/">critical-window process theorem</a> upgrades the finite-parameter law to convergence in $D([a,b],\ell^2_\downarrow)$ with the Skorokhod $J_1$ topology on every bounded parameter interval. A stopped squared-mass estimate controls short-time changes, and the proof includes compact containment in the infinite-dimensional state space. It also gives the distributional limit of the parameter-integrated squared component mass. Joint surplus evolution and convergence of the corresponding expectations remain separate.</p>



## Critical-window expectations {#section-er-critical-moment-law}

<p>The <a href="/tag/1DEZ/">critical moment theorem</a> now passes the ranked size law to every continuous function of polynomial growth in the $\ell^2$ norm. It gives the susceptibility limit uniformly on bounded critical-parameter intervals and all positive moments of each fixed ranked size. The <a href="/tag/KCRC/">path-functional theorem</a> also gives every positive moment of the parameter-integrated squared component mass. The uniform integrability comes from a complete-graph susceptibility bound and a distinct-cluster expansion; joint surplus evolution remains separate.</p>



## New cycles across the critical window {#section-er-critical-cycle-births}

<p>The <a href="/tag/6248/">cycle-birth theorem</a> couples the critical size path to its new cycle-closing edges on any bounded parameter interval. Given the limiting size path, these edges form a Poisson point process of intensity half its squared $\ell^2$ norm. A finite Poisson-proposal construction has an explicit $O(N^{-1/3})$ rejection error for the simple graph. The <a href="/tag/M7RY/">moment formulas</a> give the new cycle count's limiting mean, variance and covariance with integrated squared mass. This counts increments after the initial parameter; the full evolution of ranked component surpluses remains separate.</p>




## Weighted surplus and the initial marked tail {#section-er-critical-weighted-surplus}

<p>The <a href="/tag/1QUE/">weighted marked-state limit</a> strengthens the fixed-parameter critical law to control the sum of component mass times surplus. A <a href="/tag/RJJ9/">cycle-counting estimate</a> bounds the late exploration remainder by $1/[2(T-\lambda)^2]$. The <a href="/tag/NH8N/">inherited-mark estimate</a> then shows that an initially negligible tail remains negligible through mergers over any bounded parameter interval. These provide the initial-tail estimates needed for the ranked marked process; its full joint evolution is still separate.</p>




## The joint marked law across critical parameters {#section-er-critical-augmented-law}

<p>The <a href="/tag/JSGY/">augmented critical law</a> now identifies ranked sizes and surpluses jointly at every finite list of window parameters. Its <a href="/tag/KBJ8/">Poisson construction</a> carries old marks through mergers and assigns new cycle marks to their components. <a href="/tag/V90S/">Labelled component continuity</a> and the weighted initial-tail estimate supply the <a href="/tag/4DZC/">finite-time approximation</a>. Loops and repeated edges have an explicit vanishing comparison error for the simple graph. Marked path-space convergence remains a separate question.</p>




## Paths of total weighted surplus {#section-weighted-surplus-path-link}

<p>The <a href="/tag/EURS/">joint critical path law</a> now includes the total size-weighted surplus, with initial cycles retained. Its proof uses <a href="/tag/0DWE/">a stopped drift estimate</a> and the earlier marked finite-dimensional laws. It also gives convergence in distribution of the time-integrated weighted surplus. The result concerns this scalar sum; the path topology for the entire ranked mark sequence remains open here.</p>


## Expected critical weighted surplus {#section-critical-weighted-surplus-mean-link}

<p>The <a href="/tag/O4TX/">weighted-surplus expectation theorem</a> now passes the critical path limit to observables with linear growth in total weighted surplus, including its time integral. It uses <a href="/tag/U59P/">moment bounds for components explored early</a> and the vanishing expected late remainder. Initial surplus is included. The result does not assert higher weighted-surplus moments or the full ranked marked-path limit.</p>


## Weighted-surplus moments and mixed expectations {#section-critical-weighted-surplus-fractional-link}

<p>The <a href="/tag/WPKA/">weighted-surplus tail estimate</a> strengthens the critical first-moment limit to every moment of order strictly below two. A finite exploration cutoff makes the late mean bound uniform in graph size, and balancing it against early-component moments gives tails with exponents approaching two. The <a href="/tag/JTVN/">mixed expectation theorem</a> then permits exponential weights in squared component size together with these surplus powers, including products of the two time integrals. The second weighted-surplus moment remains outside this argument.</p>


## All weighted-surplus moments {#section-critical-weighted-surplus-all-link}

<p>The <a href="/tag/QKHG/">dyadic late-component argument</a> now bounds every positive moment of critical total weighted surplus. It combines a sharper queue estimate with the vanishing squared-mass moments of the unexplored subcritical graph. The <a href="/tag/DK7F/">moment-limit theorem</a> includes the second moment, variances, and mixed size/surplus path expectations of every polynomial surplus order. Positive exponential moments of the surplus and the full ranked marked-path topology remain separate.</p>


## Surplus across component sizes {#section-critical-surplus-measure-link}

<p>The <a href="/tag/EAQD/">measure-valued critical path limit</a> records how size-weighted surplus is distributed over component sizes, jointly with the ranked size path. Continuous tests of this measure and all polynomial moments of their time integrals converge. Its total mass recovers the earlier scalar weighted surplus; at each fixed limiting parameter, distinct component sizes identify the individual marks. Equal-size atoms are combined, so the full ranked marked-path topology remains separate.</p>


## The limit of exponential surplus estimates {#section-critical-surplus-laplace-link}

<p>The <a href="/tag/7E7T/">Brownian excursion lower bound</a> shows that critical weighted surplus has tail at least $ce^{-Cx^{3/4}}$. Its polynomial moments are finite, but every positive ordinary exponential moment is infinite; the same holds for its time integral. The <a href="/tag/B7V7/">joint size and surplus transform</a> consequently uses a Laplace sign for surplus. All mixed derivatives converge up to the closed surplus half-plane. At its boundary the surplus transform has derivatives of every order and a Taylor series of radius zero.</p>


## Excursion geometry and cycle-mark fluctuations {#section-critical-surplus-conditional-link}

<p>The <a href="/tag/OPH4/">weighted Poisson coupling</a> approximates all conditional surplus marks with expected error $O(N^{-1})$. The <a href="/tag/OWBW/">conditional-law theorem</a> retains their random excursion intensities in the critical limit and separates total weighted-surplus variance into a cycle-mark term and an excursion-geometry term. Conditional on the Brownian geometry, every exponential moment is finite. Their average can still be infinite, as the preceding lower tail bound shows.</p>


## The change in mean surplus across the window {#section-critical-surplus-drift-link}

<p>The <a href="/tag/WVGG/">exact finite-graph drift</a> retains the missing-edge correction for simple graphs. Its compensator converges to a <a href="/tag/83JM/">square-integrable surplus martingale</a>. Consequently the expected critical weighted surplus is continuously differentiable and strictly increasing, and the finite means converge together with their first parameter derivatives. The derivative separates the increases due to mergers and new cycle marks.</p>


## Evolution of the surplus profile {#section-critical-surplus-profile-link}

<p>The <a href="/tag/LX6L/">surplus profile drift</a> records both transport at mergers and the addition of new cycle marks. The <a href="/tag/E4JW/">martingale and mean equations</a> apply to bounded Lipschitz tests and polynomial weights in component size. The finite profile means converge together with their first parameter derivatives. For polynomial weights this gives an explicit hierarchy involving size moments and surplus profiles; it retains their correlations.</p>


## Fluctuations of the surplus profile {#section-critical-surplus-quadratic-variation-link}

<p>The <a href="/tag/VM8H/">finite quadratic rates</a> retain the exact missing-edge correction and give a differential equation for finite profile covariances. The <a href="/tag/XT0C/">realized quadratic variations</a> converge jointly with the critical profile paths, with convergence of all mixed polynomial moments. Their proof uses variation along the actual paths. Passing the instantaneous countable rates would require an additional squared-mark tail estimate, which is kept separate.</p>


## Predictable fluctuation rates {#section-critical-surplus-predictable-rate-link}

<p>A <a href="/tag/4W2Z/">comparison with weighted surplus one unit later</a> controls the squared-mark term in the quadratic rates. Transporting a selected initial mark tail gives the uniform rate-tail bound. The <a href="/tag/GJB6/">predictable covariation theorem</a> then identifies the compensators of the realized jump sums and proves convergence of the profile covariances together with their first parameter derivatives. These conclusions concern the critical Erdős–Rényi law; they do not extend the weighted-state topology to arbitrary states with uncontrolled squared marks.</p>


## Joint surplus transforms and higher moments {#section-critical-surplus-nonlinear-link}

<p>The <a href="/tag/BH5K/">higher jump-moment estimate</a> controls large merger increments using later weighted-surplus moments. The resulting <a href="/tag/KP1O/">nonlinear evolution theorem</a> applies to smooth functions with polynomially growing gradients of any finite collection of surplus profiles. It gives a martingale formula, compact uniform convergence of expectation derivatives, and exact equations for mixed polynomial moments and joint characteristic functions. The equations keep the correlations with the marked component state.</p>


## Sharp tail powers at criticality {#section-critical-sharp-surplus-tail-link}

<p>A <a href="/tag/X92C/">reciprocal squared-mass stopping argument</a> turns the cubic largest-component tail into an upper bound $Ce^{-cs^{3/2}}$ for squared mass. Together with a global Brownian queue estimate, it gives <a href="/tag/J2VQ/">matching upper and lower tail powers $3/4$ for weighted surplus</a>. Its $q$th norm has order $q^{4/3}$. At power $3/4$, small positive exponential parameters are integrable and sufficiently large ones are not; the exact threshold remains undetermined. The joint size/surplus and integrated laws are moment-determinate despite the zero Taylor radius of the ordinary surplus transform.</p>


## Uniform finite-graph surplus tails {#section-critical-finite-surplus-tail-link}

<p>The <a href="/tag/N81A/">full exploration-queue estimate</a> dominates adaptive discovery counts by independent binomial rows, allowing a finite analogue of the Brownian late-time argument. It yields the <a href="/tag/65IO/">uniform $Ce^{-cx^{3/4}}$ upper tail</a> for weighted surplus in critical finite complete graphs. Small positive exponential moments of $H_N^{3/4}$ now converge to those of the limit, as do all fixed positive exponential moments below that power. The path expectation theorem also permits simultaneous fractional-exponential growth in squared mass and weighted surplus.</p>


## The entire critical exploration and component shapes {#section-critical-global-shapes-link}

<p>The <a href="/tag/ZFGF/">global queue theorem</a> upgrades compact-interval exploration convergence to the uniform norm on the whole half-line, jointly with sizes and weighted surplus. The <a href="/tag/GDPT/">component-shape theorem</a> retains each excursion after normalizing its duration, with squared-size weights making a finite measure. It identifies the exact root correction between finite queue area and conditional surplus mean, and passes polynomial and small fractional-exponential geometric expectations to the limit.</p>


## Higher conditional surplus moments and transforms {#section-critical-conditional-transforms-link}

<p>The <a href="/tag/WYUD/">higher-moment Poisson coupling</a> strengthens the conditional weighted-surplus law to every finite Wasserstein distance, with an averaged error bound for the finite binomial-to-Poisson replacement. The <a href="/tag/L3KC/">conditional analytic limit</a> gives convergence of the random entire transforms and all their complex derivatives. Exact Bernoulli cumulant polynomials retain the finite-graph corrections. These conditional results coexist with divergence of every averaged positive exponential moment of total weighted surplus.</p>
