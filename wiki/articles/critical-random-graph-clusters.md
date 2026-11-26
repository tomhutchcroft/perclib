---
{
  "id": "critical-random-graph-clusters",
  "title": "Critical Erdős–Rényi components",
  "subtitle": "Exploration, progeny tails and the two-thirds scale",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "A stopped exploration comparison and uniform binomial progeny bounds give critical cluster tails. Counting vertices in large components then proves tightness of the largest component and its reciprocal on the two-thirds scale.",
  "context": [
    "Independent bond percolation on the complete graph with vertex set $[n]$.",
    "The root component includes its root. Total branching-process progeny may be infinite.",
    "In critical-window statements, $p_n=(1+\\theta n^{-1/3})/n$, with fixed $\\theta\\in\\mathbb R$ and $n$ sufficiently large that this is a probability."
  ],
  "related": [
    "finite-random-graphs",
    "branching-processes",
    "cluster-partitions",
    "universal-tightness"
  ],
  "sourceIds": [
    "heydenreich-hofstad"
  ],
  "aliases": [
    "Erdos Renyi",
    "critical random graph",
    "largest critical component",
    "binomial progeny"
  ],
  "prototypeUses": []
}
---

## Exploring a component {#section-exploration}

<p>Write $C(v)$ for the component of $v$ in $G(n,p)$, and $T_m$ for the total progeny of a Galton–Watson process started from one individual with offspring law $\operatorname{Bin}(m,p)$. Set $T_0=1$.</p>
<a id="tag-0K60" data-assertion="proposition" data-title="A component is sandwiched between binomial progeny tails up to a stopping size"></a>
<p>For $n\ge1$, $p\in[0,1]$ and integers $1\le k\le n$,</p>
<div class="math-display">$$\mathbb P(T_{n-k}\ge k)\le\mathbb P(|C(1)|\ge k)\le\mathbb P(T_n\ge k).$$</div>
<p>In fact, $|C(1)|$ is stochastically dominated by $T_n$.</p>
<p><em>Proof.</em> Start with vertex $1$ in a queue. At each step remove its first vertex and reveal its bonds to all vertices not yet discovered, adding the open neighbours to the queue. No such bond has been tested before: earlier tests had an already processed endpoint. Conditional on the past, these tests are fresh independent Bernoulli variables with parameter $p$.</p>
<p>Use an independent row of $n$ Bernoulli variables at each step, assigning the first $U$ entries to the $U$ undiscovered vertices in their fixed order. The number of new discoveries is at most the whole row sum. The queue with whole-row increments is a Galton–Watson queue with offspring law $\operatorname{Bin}(n,p)$, and cannot empty before the component queue. This proves the full upper domination, including the possible value $T_n=\infty$.</p>
<p>For the lower bound, stop the component exploration as soon as it has discovered at least $k$ vertices. Before this stopping time, $U\ge n-k$; the first $n-k$ entries in each fresh row therefore give a smaller Galton–Watson queue. If the component queue empties before discovering $k$ vertices, the smaller queue must already have emptied, with fewer than $k$ individuals in total. Thus $T_{n-k}\ge k$ forces $|C(1)|\ge k$. For $k=1$ the assertion is immediate.</p>

## Uniform progeny estimates near mean one {#section-progeny}

<a id="tag-L3AK" data-assertion="theorem" data-title="Uniform square-root progeny tails for near-critical binomial offspring"></a>
<p>Let $m\ge2$, $0<p\le1/4$, and $\lambda=mp\in[1/2,3/2]$. There is a universal $C<\infty$ such that, for every integer $k\ge1$,</p>
<div class="math-display">$$\mathbb P(T_m\ge k)\le4(\lambda-1)_++\frac C{\sqrt k}.$$</div>
<p>For each $M\ge0$ there is $c_M>0$, independent of $m,p,k$, such that</p>
<div class="math-display">$$k(\lambda-1)^2\le M\quad\Longrightarrow\quad
\mathbb P(T_m\ge k)\ge\frac{c_M}{\sqrt k}.$$</div>
<p><em>Proof.</em> By <a href="/tag/RL1L/">Dwass's formula</a>,</p>
<div class="math-display">$$\mathbb P(T_m=\ell)=\frac1\ell\mathbb P\bigl(\operatorname{Bin}(m\ell,p)=\ell-1\bigr).$$</div>
<p>A binomial variable $B\sim\operatorname{Bin}(N,p)$ has largest atom at most $C[Np(1-p)]^{-1/2}$. Indeed, Fourier inversion and</p>
<div class="math-display">$$|1-p+pe^{it}|^N
\le\exp\{-2Np(1-p)\sin^2(t/2)\}
\le\exp\{-2Np(1-p)t^2/\pi^2\},\qquad |t|\le\pi,$$</div>
<p>bound each atom by a Gaussian integral. Here $m\ell p(1-p)\ge3\ell/8$, so $\mathbb P(T_m=\ell)\le C\ell^{-3/2}$ and the sum over $\ell\ge k$ is at most $C/\sqrt k$.</p>
<p>The remaining mass is survival. Let $q=\mathbb P(T_m=\infty)$. The <a href="/tag/BFM4/">extinction criterion</a> gives $q=0$ when $\lambda\le1$; the law is nondegenerate and has a zero-offspring atom. When $q>0$, its fixed-point equation is $1-q=(1-pq)^m$, and $q<1$. Therefore</p>
<div class="math-display">$$q+\frac{q^2}{2}\le-\log(1-q)
=-m\log(1-pq)
\le\lambda q+\frac{\lambda p}{2(1-p)}q^2
\le\lambda q+\frac{q^2}{4}.$$</div>
<p>This yields $q\le4(\lambda-1)$ and proves the upper bound.</p>
<p>For the lower bound, suppose first that $k\ge2$ and take $k\le\ell\le2k-1$. Put $N=m\ell$, $j=\ell-1$ and $u=j/N$. Stirling's inequalities give an absolute $c>0$ for which</p>
<div class="math-display">$$\mathbb P(\operatorname{Bin}(N,p)=j)
\ge\frac{c}{\sqrt{Nu(1-u)}}\exp\{-ND(u\Vert p)\},$$</div>
<p>where $D(u\Vert p)=u\log(u/p)+(1-u)\log((1-u)/(1-p))$. Both $j$ and $N-j$ are positive. The inequality $\log x\le x-1$ gives</p>
<div class="math-display">$$D(u\Vert p)\le\frac{(u-p)^2}{p(1-p)},\qquad
ND(u\Vert p)\le\frac{(\ell-1-\lambda\ell)^2}{\lambda\ell(1-p)}
\le C\bigl(\ell^{-1}+\ell(\lambda-1)^2\bigr)\le C(1+2M).$$</div>
<p>Also $Nu(1-u)\le\ell$. Consequently, Dwass's formula gives $\mathbb P(T_m=\ell)\ge c_M\ell^{-3/2}$ throughout this interval. Summing its $k$ terms proves the lower bound. Decreasing $c_M$ if necessary also covers $k=1$, since $T_m\ge1$ always.</p>

## Root-cluster tails in the critical window {#section-tails}

<a id="tag-Y0FX" data-assertion="theorem" data-title="Critical-window root-cluster tails and susceptibility bounds in the complete graph"></a>
<p>Fix $\theta\in\mathbb R$ and put $p_n=(1+\theta n^{-1/3})/n$. There is a universal $C$ such that, for all sufficiently large $n$ and every integer $k\ge1$,</p>
<div class="math-display">$$\mathbb P_{p_n}(|C(1)|\ge k)
\le C\left(\theta_+n^{-1/3}+k^{-1/2}\right).$$</div>
<p>For each fixed $r>0$, there are $c(r,\theta)>0$ and $n_0(r,\theta)$ such that, for $n\ge n_0(r,\theta)$ and integers $1\le k\le rn^{2/3}$,</p>
<div class="math-display">$$\mathbb P_{p_n}(|C(1)|\ge k)\ge c(r,\theta)k^{-1/2}.$$</div>
<p>The same positive constant $c(1,\theta)$ and threshold $n_0(1,\theta)$ work for every $0<r\le1$. In particular, for some $c_\theta>0$ and all sufficiently large $n$,</p>
<div class="math-display">$$\chi_n(p_n):=\mathbb E_{p_n}|C(1)|\ge c_\theta n^{1/3}.$$</div>
<p>If $\theta<0$, then whenever $p_n\in[0,1]$ one also has $\chi_n(p_n)\le n^{1/3}/|\theta|$.</p>
<p><em>Proof.</em> Apply the upper exploration bound with $m=n$. Its offspring mean is $1+\theta n^{-1/3}$, which lies in $[1/2,3/2]$ for large $n$, and $p_n\le1/4$. The progeny estimate proves the upper tail, including $k>n$ where the component probability is zero.</p>
<p>For the lower bound, use $m=n-k$. For fixed $r,\theta$ and $k\le rn^{2/3}$, large $n$ ensures $m\ge n/2\ge2$ and</p>
<div class="math-display">$$\lambda=(n-k)p_n=1+\theta n^{-1/3}-\frac{k}{n}(1+\theta n^{-1/3}),\qquad
|\lambda-1|\le(|\theta|+2r)n^{-1/3}.$$</div>
<p>Thus $\lambda\in[1/2,3/2]$ and $k(\lambda-1)^2\le r(|\theta|+2r)^2$. The lower progeny estimate and stopped exploration give the claimed tail. Taking $r=1$ also proves the uniform assertion for smaller $r$.</p>
<p>Summing the lower tail for $1\le k\le\lfloor n^{2/3}\rfloor$ gives the susceptibility lower bound. If $\theta<0$, upper domination and the <a href="/tag/UKY4/">mean total-progeny formula</a> give</p>
<div class="math-display">$$\chi_n(p_n)\le\mathbb E T_n
=\frac1{1-np_n}=\frac{n^{1/3}}{|\theta|}.$$</div>
<p>The endpoint $p_n=0$ also satisfies this identity. This argument gives no susceptibility upper bound when $\theta\ge0$, because the dominating branching process then has infinite mean total progeny.</p>

## The largest component {#section-largest}

<p>For an integer $k\ge1$, count vertices in components of size at least $k$:</p>
<div class="math-display">$$Z_{\ge k}=\sum_{v=1}^n\mathbf1_{\{|C(v)|\ge k\}},\qquad
L_1=\max_v|C(v)|.$$</div>
<p>A component of size at least $k$ contributes all its vertices, so $\{L_1\ge k\}=\{Z_{\ge k}\ge k\}$ and $\{L_1<k\}=\{Z_{\ge k}=0\}$. Vertex symmetry gives $\mathbb E Z_{\ge k}=n\mathbb P(|C(1)|\ge k)$. Taking $F(a)=G(a)=\mathbf1_{\{a\ge k\}}$ in <a href="/tag/25Z4/">the cluster-covariance theorem</a> yields</p>
<div class="math-display">$$\operatorname{Var}(Z_{\ge k})
\le\mathbb E\sum_{C}|C|^2\mathbf1_{\{|C|\ge k\}}
=n\mathbb E[|C(1)|\mathbf1_{\{|C(1)|\ge k\}}]
\le n\chi_n(p).$$</div>
<p>The sum is over components, each counted once. The first inequality also holds without vertex symmetry, with the middle expression replaced by $\sum_v\mathbb E[|C(v)|\mathbf1_{\{|C(v)|\ge k\}}]$.</p>
<a id="tag-38XP" data-assertion="theorem" data-title="The largest critical Erdős–Rényi component and its reciprocal are tight on the two-thirds scale"></a>
<p>For each fixed $\theta\in\mathbb R$, there are $b_\theta<\infty$ and $n_0(\theta)$ such that, for all $n\ge n_0(\theta)$ and all real $A\ge1$,</p>
<div class="math-display">$$\mathbb P_{p_n}\bigl(A^{-1}n^{2/3}\le L_1\le An^{2/3}\bigr)
\ge1-\frac{b_\theta}{A},\qquad p_n=\frac{1+\theta n^{-1/3}}n.$$</div>
<p><em>Proof.</em> For the upper tail take $k=\lfloor An^{2/3}\rfloor+1$. If $k>n$ the event is empty; otherwise Markov's inequality and the root-tail bound give</p>
<div class="math-display">$$\mathbb P_{p_n}(L_1>An^{2/3})
\le\frac n k\mathbb P_{p_n}(|C(1)|\ge k)
\le C\left(\frac{\theta_+}{A}+A^{-3/2}\right).$$</div>
<p>For the lower tail put $\theta'=\min(\theta,-1)$ and $p_n'=(1+\theta'n^{-1/3})/n$. Coupling every edge by the same uniform random variable makes $L_1$ at $p_n$ at least its value at $p_n'$. It therefore suffices to work at $p_n'$, where $\chi_n(p_n')\le n^{1/3}$.</p>
<p>Write $a=A^{-1}n^{2/3}$. If $a\le1$, the event $L_1<a$ is empty. Otherwise let $k=\lceil a\rceil$, so $k\le2a\le2n^{2/3}$. The lower root-tail bound with $r=2$ and the variance estimate imply</p>
<div class="math-display">$$\mathbb E_{p_n'}Z_{\ge k}\ge\frac{cn}{\sqrt k}
\ge\frac c{\sqrt2}A^{1/2}n^{2/3},\qquad
\operatorname{Var}_{p_n'}(Z_{\ge k})\le n^{4/3}.$$</div>
<p>Since $L_1<a$ is equivalent to $Z_{\ge k}=0$, Chebyshev's inequality gives</p>
<div class="math-display">$$\mathbb P_{p_n'}(L_1<a)
\le\frac{\operatorname{Var}_{p_n'}(Z_{\ge k})}{(\mathbb E_{p_n'}Z_{\ge k})^2}
\le\frac2{c^2A}.$$</div>
<p>The choices of $n_0$ and $c=c(2,\theta')$ do not depend on $A$. Combining the tails proves the theorem.</p>
<p>This supplies a proof of the scale described in the <a href="/tag/F9EV/">finite-random-graph overview</a>. Tightness does not identify a limiting distribution or establish joint convergence of the ordered components. Those require further results; the <a href="/coverage/sources/heydenreich-hofstad-2017-random-graphs/">reading map</a> records them separately.</p>
