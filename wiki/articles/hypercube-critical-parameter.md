---
{
  "id": "hypercube-critical-parameter",
  "title": "The critical parameter of the hypercube",
  "subtitle": "Boundary growth with both common neighbours counted",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "A corrected exploration estimate locates the susceptibility-defined critical parameter of the hypercube. Together with non-backtracking mixing and a sharper short-loop bound, it proves the finite triangle estimate throughout the critical interval.",
  "context": [
    "Bonds of $Q_m=\\{0,1\\}^m$ are independently open with parameter $p$. Its volume is $N=2^m$.",
    "The intrinsic ball and sphere about $o$ are $B_k$ and $S_k$; write $b_k=\\mathbb E_p|B_k|$ and $s_k=\\mathbb E_p|S_k|$.",
    "Exact-distance events use full open-and-closed certificates and the cited finite nonmonotone Reimer theorem. The source corrections remain provisional."
  ],
  "related": [
    "hypercube-mixing",
    "finite-graph-criticality",
    "countable-reimer",
    "intrinsic-geometry",
    "bk-inequality"
  ],
  "sourceIds": [
    "hofstad-nachmias-unlacing",
    "hofstad-nachmias-hypercube",
    "heydenreich-hofstad"
  ],
  "aliases": [
    "hypercube critical probability",
    "intrinsic boundary growth",
    "unlacing hypercube percolation"
  ],
  "prototypeUses": []
}
---

## The walk estimates used by the exploration {#section-walks}

<p>Let $P_n(x,y)$ be the endpoint kernel after exactly $n$ non-backtracking steps, with $P_0=I$ and a uniformly chosen first edge. Put $q=p(m-1)$. Write $e_1$ for a vertex of Hamming weight one and $e_{12}$ for one of weight two.</p>
<a id="tag-V395" data-assertion="proposition" data-title="Fixed endpoints have uniform non-backtracking return bounds"></a>
<p>For $m\ge2$,</p>
<div class="math-display">$$P_2(0,e_{12})=\frac2{m(m-1)},\qquad P_3(0,e_1)=\frac1{m(m-1)}.$$</div>
<p>For each fixed integer $a\ge2$, there is $C_a<\infty$ such that, for every sufficiently large $m$ and every integer $t\ge a$,</p>
<div class="math-display">$$P_{2t}(0,e_{12})\le C_am^{-a-1},\qquad
P_{2t+1}(0,e_1)\le C_am^{-a-1}.$$</div>
<p><em>Proof.</em> There are two admissible two-step paths to $e_{12}$ and $m-1$ admissible three-step paths to $e_1$, giving the equalities.</p>
<p>Let $H_j$ be the Hamming weight of the walk after $j$ steps. Conditional on its full history, a downward step from weight $h$ has probability at most $h/(m-1)$; this bound also holds for the first step. Inspect the last $2a$ steps of a walk ending at weight two. Their initial weight is even and at most $2a+2$, every weight in the window is at most $2a+2$, and at least $a-1$ steps go down. For each possible initial weight and sequence of up/down steps, multiply the conditional bounds at the downward steps and use one at the others. There are only finitely many such patterns, depending on $a$, so the endpoint has weight two with probability at most $C_am^{-a+1}$. Coordinate symmetry divides this by $\binom m2$.</p>
<p>For an endpoint of weight one at time $2t+1$, the last $2a$ steps start at an odd weight, hence at least one. They contain at least $a$ downward steps and all their weights are at most $2a+1$. The same argument bounds their total probability by $C_am^{-a}$; symmetry now divides by $m$. Conditioning on the full history avoids assuming that the weight process alone is Markov.</p>

<a id="tag-0N08" data-assertion="proposition" data-title="Mixing bounds a long simple path by a truncated susceptibility"></a>
<p>On any finite transitive simple $m$-regular graph with $m\ge2$ and $N$ vertices, suppose</p>
<div class="math-display">$$\max_{x,y}\frac{P_T(x,y)+P_{T+1}(x,y)}2\le\frac{1+\xi}{N},\qquad T\ge1,\quad \xi\ge0.$$</div>
<p>Let $\mathcal P_t(x,y)$ denote the event that a simple open path of exactly $t$ edges joins $x$ to $y$. If $t\ge T+1$, then</p>
<div class="math-display">$$\mathbb P_p(\mathcal P_t(x,y))\le
\frac m{m-1}\max(1,q^{T+1})(1+\xi)\frac{b_t}{N}.$$</div>
<p><em>Proof.</em> Cut such a path after $j$ edges, for $j=T$ and $j=T+1$. Its prefix and remaining connection occur on disjoint edges. Increasing BK and a sum over simple prefixes, bounded by all non-backtracking prefixes, give</p>
<div class="math-display">$$\mathbb P_p(\mathcal P_t(x,y))
\le\frac m{m-1}q^j\sum_vP_j(x,v)\mathbb P_p(v\leftrightarrow y\text{ in at most }t-j\text{ edges}).$$</div>
<p>Enlarge the suffix bound to $t$ in both inequalities and average them. The mixing assumption bounds the averaged kernel, and transitivity makes the sum over $v$ equal to $b_t$. The empty suffix is allowed. This is the truncated form of <a href="/tag/HJAT/">HJAT</a>; the threshold $T+1$ ensures that both cuts exist.</p>

## Counting the next sphere {#section-counting}

<p>Explore all edges incident to $B_{k-2}$. This determines $B_{k-1}$ and its frontier $F=S_{k-1}$. On each possible exploration history, the unrevealed edges are independent Bernoulli variables with the original parameter: the history specifies only the revealed coordinates. Bipartiteness ensures that no edge joins two vertices of $F$.</p>
<a id="tag-N19V" data-assertion="proposition" data-title="The frontier collision bound counts undiscovered common neighbours"></a>
<p>For $k\ge2$, let $a_v$ be the number of neighbours of $v\notin B_{k-1}$ in $F$. Conditional on the history $\mathcal H_{k-1}$ above,</p>
<div class="math-display">$$\mathbb E_p(|S_k|\mid\mathcal H_{k-1})
=\sum_{v\notin B_{k-1}}[1-(1-p)^{a_v}]
\ge mp|F|-p\sum_{x\in F}|N(x)\cap B_{k-2}|
-\frac{p^2}{2}\sum_{\substack{x,y\in F\\d(x,y)=2}}c_F(x,y),$$</div>
<p>where the last sum is over ordered pairs and $c_F(x,y)=|N(x)\cap N(y)\setminus B_{k-1}|\in\{0,1,2\}$. In particular, its collision term is at most</p>
<div class="math-display">$$\frac{p^2}{2}\#\{(x,y)\text{ good}\}
+p^2\#\{(x,y)\text{ bad}\}.$$</div>
<p>Here a good pair consists of distinct frontier vertices with a common open predecessor in $S_{k-2}$; a bad pair has Hamming distance two and no such predecessor.</p>
<p><em>Proof.</em> A vertex outside the explored ball enters the next sphere if at least one of its $a_v$ incoming edges is open. Apply $1-(1-p)^a\ge ap-\binom a2p^2$ and sum. Each unordered pair of frontier vertices contributes once for each of its common neighbours outside the ball. Hypercube vertices at distance two have exactly two common neighbours. A good pair already has one inside, so contributes at most one; every other pair contributes at most two.</p>
<p>The distinction is necessary. In $Q_4$, identify a vertex with its set of nonzero coordinates. Take root $34$ and expose the two open paths $34,4,14,1$ and $34,3,23,2$, closing every other edge incident to their vertices at depths zero, one and two. Then $F=\{1,2\}$ and both common neighbours $\varnothing,12$ are undiscovered. There are six fresh incident edges and two double contacts, so the conditional expectation of the next sphere is $6p-2p^2$. Counting just one contact gives the false lower bound $6p-p^2$ for $0<p<1$. The <a href="/errata/hofstad-nachmias-unlacing/#two-common-neighbours">source entry</a> gives the version and locator.</p>

## Growth before the ball is large {#section-growth}

<a id="tag-JQGZ" data-assertion="theorem" data-title="Expected intrinsic spheres grow up to the square-root volume threshold"></a>
<p>There is a constant $K>0$ such that, for all sufficiently large $m$, at</p>
<div class="math-display">$$p_* =\frac{1+5/(2m^2)+K/m^3}{m-1},\qquad M=\frac{2^{m/2}}{m^3},$$</div>
<p>every integer $k\ge1$ with $b_k\le M$ satisfies</p>
<div class="math-display">$$s_k\ge(1+m^{-3})s_{k-1}.$$</div>
<p><em>Proof.</em> Write $q=p_*(m-1)$ and $a=1+m^{-3}$. Choose $K$ at the end. Once $m$ is sufficiently large depending on $K$,</p>
<div class="math-display">$$1\le q\le1+10m^{-2}.$$</div>
<p>All constants below are uniform over this interval. By <a href="/tag/GIF2/">GIF2</a>, one may take $T=\lceil m\log m\rceil$ in the mixing estimate, with $\xi=1/\log m$ for all sufficiently large $m$. Since $q^{2T}=1+o(1)$ uniformly, the preceding truncated path estimate has an absolute constant.</p>
<p>We induct on $k$. The first sphere has mean $s_1=mp_*$. Each weight-two vertex has two disjoint two-edge paths from the root, so</p>
<div class="math-display">$$s_2=m(m-1)p_*^2-\binom m2p_*^4,\qquad
\frac{s_2}{s_1}=q-\frac{(m-1)p_*^3}{2}
=1+\frac2{m^2}+O_K(m^{-3}).$$</div>
<p>Both initial cases satisfy the required bound. Now let $k\ge3$, assume $b_k\le M$, and apply the induction hypothesis at every earlier radius. In particular,</p>
<div class="math-display">$$s_\ell\le a^{-(k-1-\ell)}s_{k-1}\quad(0\le\ell\le k-1),\qquad
\sum_{\ell=0}^{k-2}s_\ell\le m^3s_{k-1}.$$</div>
<p>Split the backward contacts in the counting lemma into open and closed edges. For an open contact from $x\in S_{k-1}$ to $w\in B_{k-2}$, necessarily $w\in S_{k-2}$. Explore one generation earlier, revealing edges incident to $B_{k-3}$. Each such $w$ has a known open parent and therefore at most $m-1$ unrevealed incident edges. Taking their conditional expectations bounds the open-contact subtraction by</p>
<div class="math-display">$$p_*^2(m-1)s_{k-2}\le p_*^2(m-1)s_{k-1}.$$</div>
<p>These edges are unrevealed, not open after deleting every edge touching $B_{k-2}$. The latter event is impossible because $w$ belongs to that ball. The <a href="/errata/hofstad-nachmias-unlacing/#unrevealed-frontier">correction</a> also explains why the root generation was handled separately.</p>
<p>We next bound the closed contacts and the bad collision pairs. Choose geodesics from the root to their endpoints, let $w$ be their last common vertex, and put $\ell=d_\omega(o,w)$ and $t=k-1-\ell$. For a closed contact $x\sim y$, the tails have lengths $t$ and some $s\le t-1$, and $t\ge2$. For a bad pair the tails both have length $t\ge2$: if $t=1$, $w$ would be a common open predecessor. In either case the two tails have disjoint edges and avoid $B_{\ell-1}$.</p>
<p>The event $d_\omega(o,w)=\ell$ is certified by all the open and closed edge states incident to $B_{\ell-1}$. Its certificate is disjoint from the tails, including when $\ell=0$, where the certificate is empty. Apply finite nonmonotone Reimer to this event and the increasing disjoint-tail event. Thus the probability is at most $\mathbb P_p(d_\omega(o,w)=\ell)$ times the probability of the two disjoint paths. Full certificates are essential; <a href="/errata/hofstad-nachmias-unlacing/#nonmonotone-certificates">deleting edges is not the definition of nonmonotone disjoint occurrence</a>. The later EURANDOM report already corrects this definition. The finite theorem used here is the cited input in <a href="/articles/countable-reimer/#section-certificates">Reimer on a countable edge set</a>.</p>
<p>For $t\ge T+1$, increasing BK separates the two tails. Bound one by $Cb_t/N$ using the truncated mixing estimate and sum the other over its endpoint, obtaining at most $b_t$. There are $m$ adjacent choices for a closed contact and $\binom m2$ choices at distance two for a bad pair. Their respective contributions are at most</p>
<div class="math-display">$$\frac{Cp_*m}{N}\sum_{\ell=0}^{k-2}s_\ell b_t^2,
\qquad
\frac{Cp_*^2\binom m2}{N}\sum_{\ell=0}^{k-2}s_\ell b_t^2.$$</div>
<p>The sums here run only over the corresponding long-tail indices. Since $t\le k$, $b_t\le b_k\le M$, and $M^2/N=m^{-6}$, each expression is at most $Cm^{-3}s_{k-1}$.</p>
<p>For $2\le t\le T$, count the two open tails together. Concatenating them, with the first reversed, gives a non-backtracking trail: it has no repeated edge, although a vertex may repeat. If its length is $n=t+s$, its open probability is $p_*^n$. Let $P_{t,s}(x,w,y)$ be the probability that a non-backtracking walk from $x$ is at $w$ at time $t$ and at $y$ at time $t+s$. A union bound gives</p>
<div class="math-display">$$\mathbb P_p(\mathcal P_t(w,x)\circ\mathcal P_s(w,y))
\le\frac m{m-1}q^{t+s}P_{t,s}(x,w,y).$$</div>
<p>Only trails are assigned the weight $p_*^{t+s}$; their number is then bounded by the number of all non-backtracking walks. This avoids assigning that weight to a walk with repeated edges. Translation symmetry, followed by summing over the intermediate vertex, gives for $j=1,2$</p>
<div class="math-display">$$\sum_{x,y:\,d(x,y)=j}P_{t,s}(x,w,y)
=\binom mjP_{t+s}(0,e_{1\cdots j}).$$</div>
<p>Consequently, after summing over $w$ and using $s_\ell\le s_{k-1}$, the short closed-contact subtraction is at most</p>
<div class="math-display">$$\frac{p_*m^2}{m-1}s_{k-1}
\sum_{t=2}^T\sum_{s=0}^{t-1}q^{t+s}P_{t+s}(0,e_1)
\le\left(\frac2{m^2}+\frac C{m^3}\right)s_{k-1}.$$</div>
<p>Here parity removes even $t+s$. Total length three occurs in at most two pairs, $(t,s)=(2,1),(3,0)$, giving $2q^3/[m(m-1)]$. The finitely many terms of lengths five, seven and nine are $O(m^{-3})$ by the local walk bound. For all remaining lengths use its case $a=5$: there are at most $T^2$ terms, each at most $Cm^{-6}q^{2T}$, and $T^2m^{-6}=o(m^{-3})$. These estimates prove the displayed inequality with a constant independent of $K$.</p>
<p>The short bad-pair subtraction is similarly bounded by</p>
<div class="math-display">$$p_*^2\frac m{m-1}\binom m2s_{k-1}
\sum_{t=2}^Tq^{2t}P_{2t}(0,e_{12})
\le\frac C{m^3}s_{k-1}.$$</div>
<p>The terms $t=2,3$ are $O(m^{-3})$ and $O(m^{-4})$; for $t\ge4$ use the case $a=4$, giving a total $O(Tm^{-5})=o(m^{-3})$. This is the extra collision term missing from the source estimate.</p>
<p>Finally, each good pair has a common open predecessor $w\in S_{k-2}$. Sum over this predecessor, using its exact-distance certificate and the two distinct open edges. Reimer gives an expected ordered-pair count at most $m(m-1)p_*^2s_{k-2}$. Its collision subtraction is therefore at most</p>
<div class="math-display">$$\frac{m(m-1)p_*^4}{2}s_{k-2}
\le\left(\frac1{2m^2}+\frac C{m^3}\right)s_{k-1}.$$</div>
<p>Combining all terms yields, with an absolute $C$,</p>
<div class="math-display">$$s_k\ge\left[mp_*-(m-1)p_*^2-\frac5{2m^2}-\frac C{m^3}\right]s_{k-1}.$$</div>
<p>Since $mp_*-(m-1)p_*^2=q-q(q-1)/(m-1)$, and $0\le q(q-1)/(m-1)\le C_0m^{-3}$ uniformly for $q\le1+10m^{-2}$, the bracket is at least $1+(K-C-C_0)m^{-3}$. Choose $K\ge C+C_0+1$ and then take $m$ sufficiently large. This completes the induction, with the two-contact correction absorbed by the same third-order margin.</p>

## Locating the critical parameter {#section-critical}

<a id="tag-EFAQ" data-assertion="theorem" data-title="The hypercube critical parameter lies in the required narrow interval"></a>
<p>Fix $\lambda>0$. For all sufficiently large $m$, there is a unique $p_\lambda\in(0,1)$ with $\chi(p_\lambda)=\lambda2^{m/3}$. With the absolute constant $K$ above,</p>
<div class="math-display">$$1-\frac2{\lambda2^{m/3}}\le(m-1)p_\lambda
\le1+\frac5{2m^2}+\frac K{m^3}.$$</div>
<p>In particular,</p>
<div class="math-display">$$p_\lambda\le\frac1m+\frac1{m^2}+\frac7{2m^3}+O(m^{-4}),\qquad
[(m-1)p_\lambda]^{\lceil m\log m\rceil}=1+o(1).$$</div>
<p>This is an upper expansion and a coarser lower bound, not a matching three-term expansion.</p>
<p><em>Proof.</em> Susceptibility is continuous and strictly increasing from $1$ to $N$ on a connected finite graph, as proved in <a href="/tag/6JZB/">6JZB</a>. For fixed $\lambda$, the level lies strictly between these endpoints once $m$ is large.</p>
<p>At $p_*$, some radius has $b_k>M$. Otherwise the growth theorem would give $s_k\ge(1+m^{-3})^k$ for every $k$, contradicting $s_k=0$ for $k\ge N$. Thus $\chi(p_*)>M$. Since $M/(\lambda N^{1/3})=N^{1/6}/(\lambda m^3)\to\infty$, monotonicity gives $p_\lambda<p_*$.</p>
<p>If $q_\lambda=(m-1)p_\lambda<1$, count self-avoiding paths by non-backtracking walks to get</p>
<div class="math-display">$$\chi(p_\lambda)\le1+\frac{mp_\lambda}{1-q_\lambda}
=\frac{1+p_\lambda}{1-q_\lambda}\le\frac2{1-q_\lambda}.$$</div>
<p>This gives the lower bound; if $q_\lambda\ge1$ it is automatic. Expanding the upper bound for $p_\lambda$ proves the one-sided expansion. Finally $q_\lambda=1+O(m^{-2})$, with its possible negative deviation exponentially smaller, and $m\log m\,\log q_\lambda\to0$.</p>

## A sharper short-loop estimate {#section-short-loops}

<p>The following bound strengthens <a href="/tag/V1UF/">V1UF</a> without changing that assertion. Products denote matrix products of the endpoint kernels.</p>
<a id="tag-X9SI" data-assertion="proposition" data-title="The hypercube short-loop sum is of order m to the minus two plus a volume term"></a>
<p>There is an absolute constant $C$ such that, for every $m\ge32$ and integer $L\ge0$,</p>
<div class="math-display">$$\sup_{x,y}\sum_{\substack{0\le t_1,t_2,t_3\le L\\t_1+t_2+t_3\ge3}}
(P_{t_1}P_{t_2}P_{t_3})(x,y)
\le\frac C{m^2}+\frac{C(L+1)^3}{2^m}.$$</div>
<p><em>Proof.</em> Put $D=P_1$. Discarding the no-reversal restriction at one end gives $P_n\le[m/(m-1)]DP_{n-1}$ entrywise for $n\ge1$, including $P_0=I$. All these kernels commute, by the path-count recurrence. For total length three, strip three steps and obtain a fixed multiple of $D^3$. Three simple-walk steps end at a weight-one vertex in $3m-2$ ways and at a weight-three vertex in six ways, so $\sup_{x,y}D^3(x,y)\le3m^{-2}$.</p>
<p>For total length at least four, strip four steps, taking them from any nonzero coordinate of $(t_1,t_2,t_3)$. There are at most $3^4$ choices of the stripping sequence. Summing the remainders bounds this part by a fixed multiple of</p>
<div class="math-display">$$\left(D^4\Bigl(\sum_{s=0}^LP_s\Bigr)^3\right)(x,y).$$</div>
<p>For a uniformly sampled hypercube character, put $\theta=1-2|k|/m$ and $A_L(\theta)=\sum_{s=0}^L|\widehat P_s(k)|$. Fourier inversion bounds the last display by $\mathbb E[\theta^4A_L(\theta)^3]$. The two characters with $\theta=\pm1$ contribute at most $2(L+1)^3/2^m$.</p>
<p>When $|\theta|<1/2$, <a href="/tag/1PM2/">1PM2</a> gives $A_L\le1+|\theta|+\sum_{s\ge2}2(s+1)2^{-s}\le C$. Also $\mathbb E\theta^4=(3m^2-2m)/m^4$, by expanding the fourth moment of an average of independent signs. This part contributes $O(m^{-2})$.</p>
<p>For $1/2\le|\theta|<1$, the same Fourier bound gives $A_L\le C/(1-|\theta|)\le Cm$, since the nonexceptional character weights differ from the endpoints by at least $2/m$. The sign-average exponential bound gives $\mathbb P(|\theta|\ge1/2)\le2e^{-m/8}$. Its contribution is at most $Cm^3e^{-m/8}\le C'm^{-2}$ for $m\ge32$. Combining the three ranges proves the claim.</p>

## The triangle throughout the critical interval {#section-triangle}

<a id="tag-87Y4" data-assertion="theorem" data-title="The finite triangle estimate holds up to the hypercube susceptibility threshold"></a>
<p>Fix $\lambda>0$ and define $p_\lambda$ by $\chi(p_\lambda)=\lambda2^{m/3}$. There are numbers $\varepsilon_m\to0$, depending on $\lambda$ but not on $p,x,y$, such that, for all sufficiently large $m$, all $0\le p\le p_\lambda$ and all $x,y\in Q_m$,</p>
<div class="math-display">$$\sum_{u,v}\tau_p(x,u)\tau_p(u,v)\tau_p(v,y)
\le\mathbf1_{\{x=y\}}+\varepsilon_m+(3+\varepsilon_m)\frac{\chi(p)^3}{2^m}
\le\mathbf1_{\{x=y\}}+\varepsilon_m+(3+\varepsilon_m)\lambda^3.$$</div>
<p><em>Proof.</em> Take $T=\lceil m\log m\rceil$. The two-time mixing bound gives $\xi=1/\log m\to0$. The critical-parameter estimate gives $[p_\lambda(m-1)]^{T+1}=1+o(1)$, and the short-loop sum is $O(m^{-2})+O(T^3/2^m)=o(1)$. Substitute these three bounds into the explicit criterion <a href="/tag/PROF/">PROF</a>. Its path-weight constant tends to one uniformly for $p\le p_\lambda$, because it uses $\max(1,[p(m-1)]^{T+1})$. The finite-degree remainder also tends to zero. Enlarge a single nonnegative $\varepsilon_m$ to cover those remainders and the coefficient error. Finally susceptibility is increasing.</p>
<p>This proves the finite triangle estimate and the critical-parameter upper bound in prose. It does not prove the giant-component asymptotics, sprinkling statements or scaling limits. The nonmonotone Reimer theorem remains a named finite input, and no new Lean verification is asserted.</p>


## From the critical reference to a giant {#section-broad-supercritical-giant}

<p>The critical location and strong triangle estimates above now feed into the <a href="/tag/12DQ/">hypercube giant theorem</a> at $p=p_\lambda+\varepsilon/m$, with fixed $0<\lambda\le1/10$, $\varepsilon\to0$ and $\log(1/\varepsilon)=o(m^{1/3})$. Distance concentration gives an explicit family of short disjoint paths; independent sprinkling joins almost all the first-round large-cluster mass. <a href="/tag/E6FX/">The moment corollary</a> gives $\chi(p)\sim4\varepsilon^2 2^m$ and negligible squared mass outside the giant. The full regime just above the critical window still needs a different joining estimate.</p>
