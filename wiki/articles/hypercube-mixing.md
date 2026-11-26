---
{
  "id": "hypercube-mixing",
  "title": "Hypercube mixing and the finite triangle",
  "subtitle": "A scalar walk recurrence, the parity mode and an explicit percolation bound",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "The non-backtracking path recurrence gives uniform mixing on the hypercube without an operator-norm shortcut. Mixing controls long open paths, and a Fourier moment estimate supplies the hypercube short-loop bound needed for the finite triangle criterion.",
  "context": [
    "The hypercube $Q_d$ has $2^d$ vertices and degree $d$.",
    "The continuous-time walk has total jump rate one. The discrete non-backtracking walk chooses its first neighbour uniformly.",
    "Both walk estimates are proved for the hypercube. Locating its susceptibility-defined critical parameter remains a separate percolation input."
  ],
  "related": [
    "nonbacktracking-walk",
    "finite-graph-criticality",
    "bounded-degree-paths",
    "bk-inequality",
    "countable-reimer"
  ],
  "sourceIds": [
    "heydenreich-hofstad",
    "fitzner-hofstad-nbw",
    "hofstad-nachmias-hypercube"
  ],
  "aliases": [
    "hypercube uniform mixing",
    "non-backtracking parity mode",
    "finite triangle criterion"
  ],
  "prototypeUses": []
}
---

## The continuous-time benchmark {#section-continuous}

<a id="tag-2PEX" data-assertion="proposition" data-title="The continuous-time hypercube kernel has an exact uniform mixing threshold"></a>
<p>Let $S_t(x,y)$ be the transition kernel of simple random walk on $Q_d=\{0,1\}^d$, with total jump rate one, and let $h$ be the Hamming distance between $x$ and $y$. For $d\ge1$ and $t\ge0$,</p>
<div class="math-display">$$S_t(x,y)=2^{-d}(1+\rho)^{d-h}(1-\rho)^h,
\qquad \rho=e^{-2t/d}.$$</div>
<p>For $0<\xi<1$, define the uniform upper mixing time by</p>
<div class="math-display">$$T_\infty(\xi)=\inf\{t\ge0:\ \max_{x,y}S_t(x,y)\le(1+\xi)2^{-d}\}.$$</div>
<p>Then</p>
<div class="math-display">$$T_\infty(\xi)=-\frac d2\log\bigl((1+\xi)^{1/d}-1\bigr).$$</div>
<p>For fixed $\xi$, this is $(1+o(1))\frac d2\log d$ as $d\to\infty$. The same leading asymptotic holds for $\xi=1/\log d$.</p>
<p><em>Proof.</em> Give each coordinate an independent Poisson clock of rate $1/d$ and flip that coordinate whenever its clock rings. If $N$ is Poisson with mean $t/d$, then $\mathbb E(-1)^N=e^{-2t/d}$, so its even and odd probabilities are $(1+\rho)/2$ and $(1-\rho)/2$. Independence proves the kernel formula, with the usual empty-product convention at $t=0$.</p>
<p>The maximum is attained at $x=y$ and equals $2^{-d}(1+\rho)^d$. Solve the resulting scalar inequality for $t$. For fixed $\xi$, writing $a=\log(1+\xi)$ gives $e^{a/d}-1\sim a/d$. For $\xi=1/\log d$, this expression is asymptotic to $1/(d\log d)$, giving $T_\infty=\frac d2(\log d+\log\log d+o(1))$. This is a uniform upper-kernel threshold, not a total-variation mixing time.</p>

## Counting walks before estimating them {#section-recurrence}

<p>On a finite simple $m$-regular graph, $m\ge2$, let $B_n(x,y)$ count length-$n$ walks with no immediate reversal. Put $P_0=I$ and $P_n=B_n/[m(m-1)^{n-1}]$ for $n\ge1$. Thus $P_n$ is the endpoint distribution after exactly $n$ steps; its vertex kernels do not form a Markov semigroup.</p>
<a id="tag-1PM2" data-assertion="proposition" data-title="The path-count recurrence gives explicit hypercube Fourier bounds"></a>
<p>If $A$ is the adjacency matrix, then</p>
<div class="math-display">$$B_0=I,\quad B_1=A,\quad B_2=A^2-mI,\quad
B_n=AB_{n-1}-(m-1)B_{n-2}\quad(n\ge3).$$</div>
<p>In particular,</p>
<div class="math-display">$$\frac m{m-1}P_1P_t=P_{t+1}+\frac1{m-1}P_{t-1}\qquad(t\ge1).$$</div>
<p>On $Q_d$, define $\widehat P_n(k)=\sum_yP_n(0,y)(-1)^{k\cdot y}$ and $\theta=1-2|k|/d$. For $d\ge32$ and $n\ge2$,</p>
<div class="math-display">$$|\widehat P_n(k)|\le
\begin{cases}
3|\theta|^{n-1},&|\theta|\ge\tfrac12,\\
2(n+1)2^{-n},&|\theta|<\tfrac12.
\end{cases}$$</div>
<p><em>Proof.</em> Prepend one edge to a non-backtracking walk. A new violation can occur only in the first pair of steps. Removing that reversal leaves a walk with a first edge when $n\ge3$, allowing $m-1$ choices for the removed edge. For $n=2$ the remainder is empty, giving $m$ choices. This proves the recurrence by the same counting argument as <a href="/tag/0MK8/">0MK8</a>. Normalization gives the displayed identity; its case $t=1$ uses the exceptional formula for $B_2$. At $t=0$ it is false with $P_{-1}=0$. The <a href="/errata/hofstad-nachmias-hypercube/#walk-time-boundary">source-convention entry</a> records that boundary.</p>
<p>A character on $Q_d$ is an adjacency eigenvector with eigenvalue $d\theta$. Let $r_+,r_-$ be the roots of $r^2-d\theta r+(d-1)=0$ and put</p>
<div class="math-display">$$h_j=\sum_{a=0}^j r_+^{j-a}r_-^a\quad(j\ge0),\qquad h_{-1}=0.$$</div>
<p>The scalar eigenvalue $b_n$ of $B_n$ is $h_n-h_{n-2}$ for $n\ge1$: this gives $b_1=d\theta$, $b_2=d^2\theta^2-d$ and the required recurrence. The finite sum defines $h_j$ also at a repeated root, where it equals $(j+1)r_+^j$.</p>
<p>Write $R=\max(|r_+|,|r_-|)$. The root equation gives</p>
<div class="math-display">$$\frac R{d-1}\le\max\left(|\theta|,\frac1{\sqrt{d-1}}\right).$$</div>
<p>Indeed nonreal roots have modulus $\sqrt{d-1}$. In the real case one may replace $\theta$ by $|\theta|$; the larger positive root is at most $(d-1)|\theta|$, since</p>
<div class="math-display">$$d^2\theta^2-4(d-1)\le(d-2)^2\theta^2.$$</div>
<p>Also $R^2\ge d-1$. Therefore, for $n\ge2$,</p>
<div class="math-display">$$|\widehat P_n(k)|\le
\frac{(n+1)R^n+(n-1)R^{n-2}}{d(d-1)^{n-1}}
\le2(n+1)\left(\frac R{d-1}\right)^n.$$</div>
<p>This proves the middle-frequency estimate.</p>
<p>For $\theta\ge1/2$ and $d\ge32$, the roots are real and</p>
<div class="math-display">$$r_+-r_-=\sqrt{d^2\theta^2-4(d-1)}\ge d/\sqrt8,
\qquad 1\le r_-\le r_+\le d-1.$$</div>
<p>The finite-sum formula becomes</p>
<div class="math-display">$$b_n=\frac{r_+^{n-1}(r_+^2-1)-r_-^{n-1}(r_-^2-1)}{r_+-r_-}.$$</div>
<p>The numerator is nonnegative, and omitting its second term bounds $b_n$ above. Divide by $d(d-1)^{n-1}$, use $(r_+^2-1)/(d(r_+-r_-))\le\sqrt8<3$ and $r_+/(d-1)\le\theta$, and obtain the edge-frequency estimate. Finally $b_n(-\theta)=(-1)^nb_n(\theta)$, so the same bound holds for negative $\theta$.</p>
<p>No Euclidean operator norm is identified with a spectral radius in this argument. Such an identification is invalid for the directional matrix in the <a href="/errata/fitzner-hofstad-nbw/#operator-norm-spectral-radius">cited NBW proof</a>. The bounds above suffice for the mixing conclusion; they do not assert the source's sharper coefficient-one estimate.</p>

## Averaging out the parity mode {#section-mixing}

<p>Define $Q_n=(P_n+P_{n+1})/2$. The average is necessary: at the all-ones character, $\widehat P_n(\mathbf1)=(-1)^n$, so the unaveraged walk cannot approach the uniform law.</p>
<a id="tag-GIF2" data-assertion="theorem" data-title="Two consecutive non-backtracking times mix uniformly by half d log d"></a>
<p>For $d\ge32$ and $n\ge2$,</p>
<div class="math-display">$$2^d\max_{x,y}|Q_n(x,y)-2^{-d}|
\le6\bigl[(1+e^{-2(n-1)/d})^d-1\bigr]
+2^{d+1}(n+2)2^{-n}.$$</div>
<p>Consequently, for every $\varepsilon>0$, for all sufficiently large $d$, the integer $n=\lceil(1+\varepsilon)d\log d/2\rceil$ satisfies</p>
<div class="math-display">$$\max_{x,y}Q_n(x,y)\le\frac{1+1/\log d}{2^d}.$$</div>
<p><em>Proof.</em> Fourier inversion gives a sum over the $2^d$ characters. The constant coefficient is one; averaging makes the all-ones coefficient zero. The <a href="/errata/heydenreich-hofstad/#hypercube-parity-mode">parity correction</a> is precisely the removal of this second exceptional frequency.</p>
<p>For the remaining edge frequencies, pair weights $j$ and $d-j$. The preceding estimate and $1-2j/d\le e^{-2j/d}$ bound their contribution by</p>
<div class="math-display">$$6\sum_{j=1}^{\lfloor d/4\rfloor}\binom dj e^{-2j(n-1)/d}
\le6\bigl[(1+e^{-2(n-1)/d})^d-1\bigr].$$</div>
<p>Every middle coefficient of $Q_n$ has modulus at most $2(n+2)2^{-n}$, so their total is at most the second displayed term. Translation invariance makes the estimate uniform in the starting vertex.</p>
<p>At the stated value of $n$, one has $d e^{-2(n-1)/d}=O(d^{-\varepsilon})$. The first term is therefore $O(d^{-\varepsilon})=o(1/\log d)$. Since $n$ has order $d\log d$, the second term is also $o(1/\log d)$. This proves the claimed upper bound.</p>

## Long open paths after mixing {#section-long-paths}

<p>Let $G$ be a finite transitive simple graph with $N$ vertices and degree $m\ge2$. Take independent bonds with common parameter $p\in[0,1]$. Write $\tau(x,y)=\mathbb P_p(x\leftrightarrow y)$ and $\chi=\sum_y\tau(x,y)$. For an integer $T\ge1$, let $L_T(x,y)$ be the probability of a simple open $x$–$y$ path of length at least $T+1$. This event does not require that every open path be long.</p>
<a id="tag-HJAT" data-assertion="proposition" data-title="Averaged non-backtracking mixing bounds long open paths uniformly"></a>
<p>Suppose $\xi\ge0$ and</p>
<div class="math-display">$$\max_{x,y}\frac{P_T(x,y)+P_{T+1}(x,y)}2\le\frac{1+\xi}{N}.$$</div>
<p>Put $q=p(m-1)$ and $C=\frac m{m-1}\max(1,q^{T+1})$. Then, for every $x,y$,</p>
<div class="math-display">$$L_T(x,y)\le C(1+\xi)\frac\chi N.$$</div>
<p><em>Proof.</em> A simple path counted by $L_T$ can be split after either $T$ or $T+1$ edges. Fix a simple prefix of length $\ell$ ending at $v$. Its open-edge event and the connection from $v$ to $y$ occur disjointly on the original path, including when the suffix is empty. <a href="/tag/JRCI/">BK</a> bounds this probability by $p^\ell\tau(v,y)$. Sum over simple prefixes and bound their number by $B_\ell(x,v)$. Thus, for both $\ell=T,T+1$,</p>
<div class="math-display">$$L_T(x,y)\le\sum_vp^\ell B_\ell(x,v)\tau(v,y)
\le C\sum_vP_\ell(x,v)\tau(v,y).$$</div>
<p>Average the two bounds and apply the mixing hypothesis. Symmetry and transitivity give $\sum_v\tau(v,y)=\chi$.</p>
<p>The length threshold is $T+1$, so both cuts exist. No exact-distance event or decreasing certificate is needed for this estimate. Bounds that also prescribe a geodesic length require the nonmonotone argument separately; the <a href="/articles/countable-reimer/">countable Reimer article</a> supplies the relevant closed-edge certificate method.</p>

## An explicit finite-triangle criterion {#section-triangle}

<p>Keep the preceding assumptions and define</p>
<div class="math-display">$$R_T(x,y)=
\sum_{\substack{0\le t_1,t_2,t_3\le T\\t_1+t_2+t_3\ge3}}
\sum_{u,v}P_{t_1}(x,u)P_{t_2}(u,v)P_{t_3}(v,y).$$</div>
<a id="tag-PROF" data-assertion="theorem" data-title="Mixing and a short-loop sum imply an explicit finite-triangle bound"></a>
<p>For $\Delta_p(x,y)=\sum_{u,v}\tau(x,u)\tau(u,v)\tau(v,y)$,</p>
<div class="math-display">$$\Delta_p(x,y)\le
C^3\left[\mathbf1_{\{x=y\}}+\frac6m+\frac3{m-1}+R_T(x,y)\right]
+3C(1+\xi)\frac{\chi^3}{N}.$$</div>
<p>In particular, consider a sequence of such graphs with $m\to\infty$, integers $T\ge1$, $\xi\to0$ and parameters $p_*$ such that</p>
<div class="math-display">$$[p_*(m-1)]^T=1+o(1),\qquad
\sup_{x,y}R_T(x,y)=o(1).$$</div>
<p>Uniformly for $0\le p\le p_*$ and all $x,y$,</p>
<div class="math-display">$$\Delta_p(x,y)\le\mathbf1_{\{x=y\}}+o(1)
+(3+o(1))\frac{\chi(p)^3}{N}.$$</div>
<p>If also $\chi(p_*)=\lambda N^{1/3}$ for fixed $\lambda>0$, the final volume term is at most $(3+o(1))\lambda^3$ throughout that interval.</p>
<p><em>Proof.</em> Let $S_T(x,y)$ be the probability that the intrinsic distance is at most $T$, with distance infinity when disconnected. Then $S_T\le\tau$ and $\tau-S_T\le L_T$. Expanding the difference of the three-factor products, with every remaining factor bounded by $\tau$, shows that the triangle sum is at most the sum with all factors $S_T$, plus</p>
<div class="math-display">$$\sum_{u,v}\bigl[L_T(x,u)\tau(u,v)\tau(v,y)
+\tau(x,u)L_T(u,v)\tau(v,y)
+\tau(x,u)\tau(u,v)L_T(v,y)\bigr].$$</div>
<p>The long-path bound makes each of these three sums at most $C(1+\xi)\chi^3/N$.</p>
<p>For the short part, sum over simple paths of each length, including the empty path:</p>
<div class="math-display">$$S_T(x,y)\le\sum_{t=0}^T p^tB_t(x,y)
\le C\sum_{t=0}^T P_t(x,y).$$</div>
<p>The zero-step term is interpreted as $I$ also at $p=0$, and its coefficient one is at most $C$. After multiplying the three sums, total length zero contributes $\mathbf1_{\{x=y\}}$. Total length one contributes $3P_1(x,y)\le3/m$. Total length two contributes at most $3P_2(x,y)+3(P_1^2)(x,y)$, whether or not $T\ge2$. There are at most $m$ two-step paths to a specified endpoint, so $P_2(x,y)\le1/(m-1)$ and $(P_1^2)(x,y)\le1/m$. All larger total lengths form $R_T$. This proves the explicit estimate.</p>
<p>For the asymptotic statement, let $q_*=p_*(m-1)$. The hypothesis $q_*^T\to1$ implies $T\log q_*\to0$ and hence $(T+1)\log q_*\to0$, because $T\ge1$. Thus $C=1+o(1)$ uniformly for $p\le p_*$. The resulting upper estimate does not assert $[p(m-1)]^t\to1$ for every smaller $p$; that equality fails already at $p=0$ and $t>0$. Only the <a href="/errata/heydenreich-hofstad/#finite-triangle-uniform-upper-bound">uniform upper bound</a> is needed. Substitute the hypotheses and use monotonicity of $\chi$ for the last assertion.</p>


## The hypercube short-loop sum {#section-short-loops}

<a id="tag-V1UF" data-assertion="theorem" data-title="Hypercube short-loop sums vanish throughout polynomial time scales"></a>
<p>There is an absolute constant $K<\infty$ such that, on $Q_d$, for every $d\ge32$ and integer $T\ge0$, the sum defined above satisfies</p>
<div class="math-display">$$\sup_{x,y}R_T(x,y)\le Kd^{-3/2}
+2(T+1)^3e^{-d/8}.$$</div>
<p>In particular, it tends to zero when $T=O(d\log d)$.</p>
<p><em>Proof.</em> The kernels $P_t$ are translation invariant, so matrix multiplication becomes multiplication of Fourier coefficients. Fourier inversion and the triangle inequality give</p>
<div class="math-display">$$R_T(x,y)\le2^{-d}\sum_{k\in Q_d}
\sum_{\substack{0\le t_1,t_2,t_3\le T\\t_1+t_2+t_3\ge3}}
|\widehat P_{t_1}(k)\widehat P_{t_2}(k)\widehat P_{t_3}(k)|.$$</div>
<p>Regard the character $k$ as uniform on $Q_d$. Then $\theta=1-2|k|/d$ is the average of $d$ independent uniform signs. On $|\theta|\le1/2$, put $\rho=\max(|\theta|,(d-1)^{-1/2})\le1/2$. The general root estimate in the recurrence proof gives</p>
<div class="math-display">$$|\widehat P_t(k)|\le2(t+1)\rho^t\qquad(t\ge0),$$</div>
<p>where $t=0,1$ follow directly from $\widehat P_0=1$ and $\widehat P_1=\theta$. Sum by total length $s$ and extend to all nonnegative triples. The resulting bound is</p>
<div class="math-display">$$8\sum_{s\ge3}\binom{s+5}{5}\rho^s
=8\bigl[(1-\rho)^{-6}-1-6\rho-21\rho^2\bigr]
\le K_0\rho^3.$$</div>
<p>The last inequality follows from Taylor's formula on $[0,1/2]$, since the third derivative of $(1-\rho)^{-6}$ is bounded there. Independence and centering of the signs give $\mathbb E\theta^4=(3d^2-2d)/d^4$. Hölder's inequality therefore yields</p>
<div class="math-display">$$\mathbb E\rho^3\le\mathbb E|\theta|^3+(d-1)^{-3/2}
\le3^{3/4}d^{-3/2}+(d-1)^{-3/2}.$$</div>
<p>This bounds the contribution of the middle characters by $Kd^{-3/2}$.</p>
<p>On the remaining characters, use only $|\widehat P_t(k)|\le1$, which follows because $P_t(0,\cdot)$ is a probability distribution. There are at most $(T+1)^3$ triples. The exponential estimate</p>
<div class="math-display">$$\mathbb P(|\theta|>1/2)\le2e^{-d/8}$$</div>
<p>follows from $\mathbb E e^{a d\theta}=(\cosh a)^d\le e^{da^2/2}$, Markov's inequality with $a=1/2$, and symmetry. This includes the constant and parity characters; their coefficients need not decay. Combining the two parts proves the bound.</p>
<p>Choose $T=\lceil(1+\varepsilon)d\log d/2\rceil$. The mixing theorem and this estimate supply both walk inputs to the finite-triangle criterion. To apply it at the susceptibility-defined $p_\lambda$, one still needs $[p_\lambda(d-1)]^T=1+o(1)$. The critical-parameter estimate, the lower-window estimates and the giant-component argument remain separate in the <a href="/coverage/sources/hypercube-mixing/">reading map</a>.</p>
