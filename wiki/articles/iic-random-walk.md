---
{
  "id": "iic-random-walk",
  "title": "Random walk on incipient clusters",
  "subtitle": "Resistance, exit times and spectral dimension",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "Quadratic intrinsic volume and linear resistance imply cubic mean exit times and spectral dimension four thirds. The proof uses killed Green functions and a lazy-walk energy bound, then removes laziness at even times.",
  "context": [
    "The deterministic estimates concern an infinite connected locally finite simple graph with unit edge conductances.",
    "Walk probabilities are normalized by vertex degree when treated as heat kernels.",
    "The percolation application concerns the susceptibility-biased and ratio-controlled distant-point cylinder limits already constructed in the wiki."
  ],
  "related": [
    "incipient-cluster-limits",
    "intrinsic-geometry",
    "critical-arm-bounds",
    "triangle-susceptibility"
  ],
  "sourceIds": [
    "barlow-jarai-kumagai-slade-iic-2008",
    "kozma-nachmias-alexander-orbach-2009"
  ],
  "aliases": [
    "Alexander–Orbach",
    "spectral dimension",
    "IIC random walk",
    "intrinsic exit time"
  ],
  "prototypeUses": []
}
---

## Graph and walk conventions {#section-conventions}

<p>Fix an infinite connected locally finite simple graph $G$, a vertex $o$, and unit conductances on its edges. Write $\pi(x)=\deg_G(x)$ and</p>
<div class="math-display">$$B(r)=\{x:d_G(o,x)\le r\},\quad
S(r)=\{x:d_G(o,x)=r\},\quad
V(r)=\sum_{x\in B(r)}\pi(x).$$</div>
<p>The balls are finite. Let $X$ be ordinary simple random walk, with transition operator $P$, and let $Y$ be the lazy walk with operator $Q=(I+P)/2$. Their degree-normalized kernels are</p>
<div class="math-display">$$q_n(x,y)=\frac{\mathbf P_x(X_n=y)}{\pi(y)},\qquad
\widehat q_n(x,y)=\frac{\mathbf P_x(Y_n=y)}{\pi(y)}.$$</div>
<p>Both are symmetric. Walk expectations on this fixed graph are denoted by $\mathbf E_x$; they are distinct from expectation over a random cluster. For an integer $r\ge1$, put $D_r=B(r-1)$ and let $T_r$ and $\widehat T_r$ be the first hitting times of $S(r)$ by $X$ and $Y$, respectively. Let $\mathcal R(r)$ be the unit-conductance resistance from $o$ to the wired sphere $S(r)$. These are the same intrinsic balls and resistances as in <a href="/tag/POD2/">POD2</a>.</p>
<p>The argument below reconstructs the Green-function and heat-kernel estimates used by Barlow–Járai–Kumagai–Slade in Section 2.1 of their 31 August 2007 manuscript. Only logarithmic exponents are sought here. A lazy operator makes the energy calculation short; a final binomial comparison recovers ordinary walk at even times.</p>

## Green functions and mean exit times {#section-green-exit}

<a id="tag-331W" data-assertion="theorem" data-title="Killed Green functions give resistance and intrinsic mean exit-time bounds"></a>
<p>For $r\ge1$, define</p>
<div class="math-display">$$g_r(x,y)=\frac1{\pi(y)}\mathbf E_x\sum_{n<T_r}\mathbf1_{\{X_n=y\}}
\qquad(x,y\in D_r),$$</div>
<p>and extend it by zero at the wired boundary. Then $g_r(o,o)=\mathcal R(r)$, and</p>
<div class="math-display">$$\frac{\mathcal R(r)}2\,
V\!\left(\left\lfloor\frac{\mathcal R(r)}4\right\rfloor\right)
\le\mathbf E_oT_r\le\mathcal R(r)V(r-1)\le rV(r-1),$$</div>
<div class="math-display">$$\sup_{x\in D_r}\mathbf E_xT_r\le2rV(r-1).$$</div>
<p>For the lazy walk these mean exit times are exactly twice those for ordinary walk. If $T_o^+=\inf\{n\ge1:X_n=o\}$, then</p>
<div class="math-display">$$\mathbf P_o(T_r<T_o^+)=\frac1{\pi(o)\mathcal R(r)}.$$</div>
<p>In particular, the walk is recurrent if and only if $\mathcal R(r)\to\infty$.</p>
<p><em>Proof.</em> Every vertex of the finite set $D_r$ has a finite path to $S(r)$. Thus there is a uniform positive chance of leaving $D_r$ within a fixed finite number of steps, and the killed Green series converges. Reversibility makes $g_r$ symmetric. The function $u(y)=g_r(o,y)$ solves the finite Dirichlet system</p>
<div class="math-display">$$\sum_{z:z\sim y}\bigl(u(y)-u(z)\bigr)=\mathbf1_{\{y=o\}}\quad(y\in D_r),
\qquad u=0\quad\text{on }S(r).$$</div>
<p>Consequently the gradient of $u$ is a unit flow from $o$ to the wired sphere. Summation by parts gives</p>
<div class="math-display">$$\mathcal E(u):=\sum_{\{x,y\}\in E(G)}(u(x)-u(y))^2=u(o),$$</div>
<p>where $u$ is extended by zero outside $D_r$. If $i$ is any other unit flow, its difference from this gradient has zero divergence at every unwired vertex. Summation by parts makes the two flows orthogonal in edge space. Hence $\sum_e i(e)^2\ge\mathcal E(u)$, with equality for the gradient. The minimum-energy definition of resistance therefore gives $u(o)=\mathcal R(r)$.</p>
<p>The maximum principle gives $0\le u(y)\le u(o)$. Along a shortest path to $y$, Cauchy–Schwarz gives</p>
<div class="math-display">$$|u(o)-u(y)|^2\le d_G(o,y)\mathcal E(u)
=d_G(o,y)\mathcal R(r).$$</div>
<p>Thus $u(y)\ge\mathcal R(r)/2$ whenever $d_G(o,y)\le\mathcal R(r)/4$. A unit flow along a length-$r$ root path gives $\mathcal R(r)\le r$, so this smaller ball lies in $D_r$. Summing the occupation formula</p>
<div class="math-display">$$\mathbf E_oT_r=\sum_{y\in D_r}\pi(y)g_r(o,y)$$</div>
<p>over the smaller ball proves the lower bound; the maximum principle proves the upper bound. From any $x\in D_r$ there is a path to the wired boundary of length at most $2r$, obtained through $o$. Applying the same diagonal identity and maximum principle with source $x$ gives the supremum bound. The lazy walk inserts independent waiting times of mean two before the ordinary jumps, proving its mean-exit assertion.</p>
<p>Successive visits to $o$ before $T_r$ form a geometric count with success probability $\mathbf P_o(T_r<T_o^+)$. Its expectation is $\pi(o)g_r(o,o)$, which proves the displayed probability identity. As $r\to\infty$, the events $\{T_r<T_o^+\}$ decrease to nonreturn, up to a null set: every finite ball is exited almost surely, and a finite return path has bounded radius. Their limiting probability is zero exactly when $\mathcal R(r)\to\infty$.</p>

## Upper and lower return bounds {#section-return-bounds}

<a id="tag-KGNK" data-assertion="theorem" data-title="An energy bound and an exit-time bound control the lazy return kernel"></a>
<p>For all integers $n,r\ge1$,</p>
<div class="math-display">$$\widehat q_n(o,o)\le\frac2{V(r)}+\frac{2r}{n+1}.$$</div>
<p>Put $u_r=\mathbf E_o\widehat T_r$ and $M_r=\sup_{x\in D_r}\mathbf E_x\widehat T_r$. Then</p>
<div class="math-display">$$\widehat q_{2n}(o,o)\ge
\frac{(u_r-n)_+^2}{M_r^2V(r-1)}.$$</div>
<p><em>Proof.</em> Regard $Q$ as a self-adjoint contraction on $\ell^2(\pi)$. Its spectrum lies in $[0,1]$. For $h=\mathbf1_{\{o\}}/\pi(o)$, let $\nu$ be its spectral measure and put $f_n=Q^nh=\widehat q_n(o,\cdot)$. The spectral theorem and $(1-t)t^n\le1/(n+1)$ for $0\le t\le1$ give</p>
<div class="math-display">$$\begin{aligned}
\mathcal E(f_n)
&=2\langle f_n,(I-Q)f_n\rangle_{\ell^2(\pi)}
=2\int_0^1(1-t)t^{2n}\,d\nu(t)\\
&\le\frac2{n+1}\int_0^1t^n\,d\nu(t)
=\frac{2f_n(o)}{n+1}.
\end{aligned}$$</div>
<p>The factor two comes from laziness; $\mathcal E$ still counts each unit-conductance edge once. Since $\sum_y\pi(y)f_n(y)=1$, some $y\in B(r)$ satisfies $f_n(y)\le1/V(r)$. Cauchy–Schwarz along a path of length at most $r$ then gives, with $a=f_n(o)$,</p>
<div class="math-display">$$a\le\frac1{V(r)}+\sqrt{\frac{2ra}{n+1}}
\le\frac1{V(r)}+\frac a2+\frac r{n+1}.$$</div>
<p>Rearrangement proves the upper bound.</p>
<p>For the lower bound, the Markov property at time $n$ gives</p>
<div class="math-display">$$u_r\le n+M_r\mathbf P_o(\widehat T_r>n).$$</div>
<p>Survival inside $D_r$ implies $Y_n\in D_r$. Symmetry, the semigroup identity and Cauchy–Schwarz give</p>
<div class="math-display">$$\widehat q_{2n}(o,o)
=\sum_y\pi(y)\widehat q_n(o,y)^2
\ge\frac{\mathbf P_o(Y_n\in D_r)^2}{V(r-1)}
\ge\frac{\mathbf P_o(\widehat T_r>n)^2}{V(r-1)}.$$</div>
<p>Combining these inequalities proves the claim. A large mean exit time alone would not give this survival estimate: the bound on the supremum of mean exit times is also needed.</p>

## The deterministic exponent implication {#section-deterministic-exponents}

<a id="tag-NNW7" data-assertion="theorem" data-title="Quadratic degree volume and linear resistance imply spectral dimension four thirds"></a>
<p>Suppose, on the fixed graph,</p>
<div class="math-display">$$\lim_{r\to\infty}\frac{\log V(r)}{\log r}=2,
\qquad
\lim_{r\to\infty}\frac{\log\mathcal R(r)}{\log r}=1.$$</div>
<p>Then the walk is recurrent and</p>
<div class="math-display">$$\lim_{r\to\infty}\frac{\log\mathbf E_oT_r}{\log r}=3,
\qquad
\lim_{n\to\infty}\frac{\log\widehat q_n(o,o)}{\log n}
=\lim_{n\to\infty}\frac{\log\mathbf P_o(X_{2n}=o)}{\log n}
=-\frac23.$$</div>
<p>Thus the spectral dimension, defined by</p>
<div class="math-display">$$d_s=-2\lim_{n\to\infty}
\frac{\log\mathbf P_o(X_{2n}=o)}{\log n},$$</div>
<p>exists and equals $4/3$.</p>
<p><em>Proof.</em> Write $V(r)=r^{2+o(1)}$ and $\mathcal R(r)=r^{1+o(1)}$. The radius $s_r=\lfloor\mathcal R(r)/4\rfloor$ tends to infinity and satisfies $\log s_r/\log r\to1$. Hence $V(s_r)=r^{2+o(1)}$. Both sides of 331W now give</p>
<div class="math-display">$$\mathbf E_oT_r=r^{3+o(1)},\qquad
u_r=r^{3+o(1)},\qquad M_r=r^{3+o(1)}.$$</div>
<p>For the last equality use $u_r\le M_r\le4rV(r-1)$, and note that $V(r-1)=r^{2+o(1)}$. Recurrence also follows from 331W.</p>
<p>Taking $r=\lfloor n^{1/3}\rfloor$ in KGNK gives $\widehat q_n(o,o)\le n^{-2/3+o(1)}$. To prove the reverse logarithmic bound, fix $0<\delta<3$ and take $r=\lceil n^{1/(3-\delta)}\rceil$. Then $u_r/n\to\infty$, so for all large $n$,</p>
<div class="math-display">$$\widehat q_{2n}(o,o)
\ge\frac{u_r^2}{4M_r^2V(r-1)}
=r^{-2+o(1)}
=n^{-2/(3-\delta)+o(1)}.$$</div>
<p>Let $\delta\downarrow0$. This proves the logarithmic limit at even times for the lazy walk. The spectral representation makes $\widehat q_n(o,o)$ nonincreasing in $n$, so the same limit holds at every integer time.</p>
<p>It remains to remove laziness. The spectral measure of $P$ at $h$ is supported on $[-1,1]$, and $q_k(o,o)=\langle h,P^kh\rangle$. In particular $q_{2m}(o,o)$ is nonincreasing in $m$. In the binomial expansion of $Q^{2n}$, the total weight of the even powers is $1/2$, and all return probabilities are nonnegative. Therefore</p>
<div class="math-display">$$q_{2n}(o,o)\le2\widehat q_{2n}(o,o).$$</div>
<p>Conversely, the spectral representation gives $q_k(o,o)\le q_{2n}(o,o)$ whenever $k\ge2n$, since $t^k\le|t|^{2n}$ on $[-1,1]$. All other terms are at most $q_0(o,o)=1/\pi(o)$. If $K_n$ has binomial law with parameters $8n$ and $1/2$, Markov's inequality applied to $3^{-K_n}$ gives</p>
<div class="math-display">$$\mathbf P(K_n<2n)\le3^{2n}\mathbf E3^{-K_n}
=\left(\frac{256}{729}\right)^n.$$</div>
<p>Expanding $Q^{8n}$ consequently gives</p>
<div class="math-display">$$\widehat q_{8n}(o,o)-\frac1{\pi(o)}\left(\frac{256}{729}\right)^n
\le q_{2n}(o,o)\le2\widehat q_{2n}(o,o).$$</div>
<p>The subtracted exponential term is negligible compared with the established polynomial lower bound. Thus $q_{2n}(o,o)$ has the same logarithmic exponent. Multiplication by the fixed degree $\pi(o)$ gives the asserted ordinary return-probability limit. Using even times avoids any claim about odd-time returns on a bipartite graph.</p>

## Application to the incipient limits {#section-iic-spectral-dimension}

<a id="tag-IXCJ" data-assertion="theorem" data-title="Finite-triangle incipient cylinder limits have spectral dimension four thirds"></a>
<p>Let $d\ge2$ and suppose nearest-neighbour percolation on $\mathbb Z^d$ satisfies $\Delta_{p_c}(0)<\infty$. Let $\mu$ be either a cylinder limit of the susceptibility-biased laws $Q_p$ as $p\uparrow p_c$, or a cylinder limit of $\mathbb P_{p_c}(\,\cdot\mid0\leftrightarrow x_j)$ where $|x_j|\to\infty$, $\tau_{p_c}(x_j)>0$ and</p>
<div class="math-display">$$\frac{\tau_{p_c}(x_j-z)}{\tau_{p_c}(x_j)}\longrightarrow1
\qquad\text{for every fixed }z\in\mathbb Z^d.$$</div>
<p>For $\mu$-almost every configuration $\omega$, ordinary simple random walk on its open root cluster is recurrent and satisfies</p>
<div class="math-display">$$\lim_{r\to\infty}\frac{\log\mathbf E_0^\omega T_r}{\log r}=3,
\qquad
\lim_{n\to\infty}\frac{\log\mathbf P_0^\omega(X_{2n}=0)}{\log n}=-\frac23,
\qquad d_s=\frac43.$$</div>
<p>Here $T_r$ is the first hit of intrinsic distance $r$. The same mean-exit and return exponents hold for the lazy walk, with its return limit taken over all integer times.</p>
<p><em>Proof.</em> The <a href="/tag/E22E/">escape theorem</a> gives an infinite connected root cluster. On it every degree lies between one and $2d$, so its degree volume satisfies</p>
<div class="math-display">$$|B_\omega(r)|\le V_\omega(r)\le2d|B_\omega(r)|.$$</div>
<p><a href="/tag/RG3Z/">RG3Z</a> therefore gives the degree-volume exponent two, and <a href="/tag/POD2/">POD2</a> gives resistance exponent one. For each configuration in this common full-measure set, apply the deterministic theorem NNW7. The exceptional set concerns the percolation law; the expectations and probabilities in the conclusions are then taken over walk paths on that fixed cluster.</p>
<p>The susceptibility-biased case needs no spatial two-point estimate or uniqueness of the IIC construction. The distant-point case retains its explicit ratio assumption. These conclusions do not identify different cylinder limits, prove an annealed return asymptotic, or determine the almost-sure displacement or range of a walk. In particular, the mean exit-time exponent is not being substituted for a sample-path exit-time theorem. The spectral-dimension and quenched mean-exit questions left separate in the <a href="/articles/incipient-cluster-limits/#section-intrinsic-resistance">earlier geometry article</a> are settled here by the displayed arguments.</p>


## Hitting a nearby vertex before exit {#section-nearby-hitting}

<p>The mean-exit estimate becomes a pathwise estimate once we control the chance of escaping without returning to the root. The same comparison will show that the walk visits a substantial part of a smaller ball before exit. Keep the graph, degree volume and ordinary walk conventions above, and put $T_y=\inf\{n\ge0:X_n=y\}$.</p>

<a id="tag-LCUN" data-assertion="theorem" data-title="The killed Green function bounds the probability of missing a nearby vertex"></a>
<p>Let $r\ge1$, $y\in D_r$, $a=d_G(o,y)$ and $R=\mathcal R(r)$. Then</p>
<div class="math-display">$$\mathbf P_y(T_r<T_o)\le\frac aR.$$</div>
<p>If $a<R$, then also</p>
<div class="math-display">$$\mathbf P_o(T_r<T_y)\le\frac a{R-a}.$$</div>
<p><em>Proof.</em> Write $g=g_r(o,y)$ and $R_y=g_r(y,y)$. The strong Markov property at the first hit of a vertex, together with symmetry of the killed Green kernel, gives</p>
<div class="math-display">$$g=R\,\mathbf P_y(T_o<T_r)
=R_y\,\mathbf P_o(T_y<T_r).$$</div>
<p>In particular $g\le\min\{R,R_y\}$. On the finite graph with $S(r)$ wired, the potential $g_r(o,\cdot)-g_r(y,\cdot)$ carries unit current from $o$ to $y$. The flow calculation in 331W therefore gives</p>
<div class="math-display">$$R_{\mathrm{wired}}(o,y)=R+R_y-2g\le a,$$</div>
<p>where the last inequality follows by sending unit current along a shortest $o$-to-$y$ path. Both $R-g$ and $R_y-g$ are nonnegative, so each is at most $a$, and $R_y\ge R-a$. Divide the first difference by $R$ and the second by $R_y$. If $y=o$, both missing probabilities are zero and the conclusions hold directly.</p>

## Exit times along a walk path {#section-pathwise-exit}

<p>For the remainder of the deterministic argument assume the hypotheses of NNW7:</p>
<div class="math-display">$$V(r)=r^{2+o(1)},\qquad\mathcal R(r)=r^{1+o(1)}.$$</div>
<p>Let $L_n=\max_{0\le k\le n}d_G(o,X_k)$ be the maximum distance reached by time $n$.</p>

<a id="tag-7WII" data-assertion="theorem" data-title="Quadratic volume and linear resistance give pathwise cubic exit times and maximal displacement exponent one third"></a>
<p>Under these deterministic hypotheses,</p>
<div class="math-display">$$\lim_{r\to\infty}\frac{\log T_r}{\log r}=3,
\qquad
\lim_{n\to\infty}\frac{\log(1+L_n)}{\log n}=\frac13
\qquad\mathbf P_o\text{-almost surely}.$$</div>
<p>For the position at a single time the conclusion is instead</p>
<div class="math-display">$$\frac{\log(1+d_G(o,X_n))}{\log n}
\longrightarrow\frac13\quad\text{in }\mathbf P_o\text{-probability}.$$</div>
<p><em>Proof.</em> Put $m(s)=\mathbf E_oT_s$ and $m_*(s)=\sup_{x\in D_s}\mathbf E_xT_s$. First take integers $1\le s<r$ and $0\le t<m(s)$. Set $a_x=\mathbf P_x(T_r\le t)$ and $q=\max_{y\in S(s)}\mathbf P_y(T_r<T_o)$. Stopping first at the root shows $a_y\le q+a_o$ for $y\in S(s)$. Any path from the root to $S(r)$ must first hit $S(s)$, so the strong Markov property gives</p>
<div class="math-display">$$a_o\le\mathbf P_o(T_s\le t)(q+a_o),\qquad
a_o\mathbf P_o(T_s>t)\le q.$$</div>
<p>The same mean-exit decomposition used in KGNK, now for ordinary walk, gives $\mathbf P_o(T_s>t)\ge(m(s)-t)/m_*(s)$. LCUN gives $q\le s/\mathcal R(r)$. Hence</p>
<div class="math-display">$$\mathbf P_o(T_r\le t)
\le\frac{s\,m_*(s)}{\mathcal R(r)(m(s)-t)}.\tag{*}$$</div>
<p>By 331W and NNW7, $m(s)=s^{3+o(1)}$ and $m_*(s)=s^{3+o(1)}$. Fix $0<\varepsilon<3$ and choose $s=\lfloor r^{1-\varepsilon/6}\rfloor$, $t=\lfloor r^{3-\varepsilon}\rfloor$. Then $m(s)=r^{3-\varepsilon/2+o(1)}$, so $t\le m(s)/2$ eventually. Substitution in (*) and Markov's inequality for the opposite tail give</p>
<div class="math-display">$$\mathbf P_o(T_r\le r^{3-\varepsilon})
\le r^{-\varepsilon/6+o(1)},\qquad
\mathbf P_o(T_r\ge r^{3+\varepsilon})
\le r^{-\varepsilon+o(1)}.$$</div>
<p>Both bounds are summable along $r=2^j$. Borel–Cantelli, monotonicity of $T_r$ in $r$, and a countable sequence of positive $\varepsilon$ tending to zero prove the first almost-sure limit at every integer radius. Since $\{T_r\le n\}=\{L_n\ge r\}$, inversion gives the maximum-distance limit.</p>
<p>For the remaining claim, the upper bound follows from $d_G(o,X_n)\le L_n$. For $0<\varepsilon<1/3$, put $s=\lfloor n^{1/3-\varepsilon}\rfloor$. Reversibility and Cauchy–Schwarz give</p>
<div class="math-display">$$\mathbf P_o(X_n\in B(s))^2
\le V(s)\sum_y\pi(y)q_n(o,y)^2
=V(s)q_{2n}(o,o)=n^{-2\varepsilon+o(1)},$$</div>
<p>using NNW7 for the return exponent. This proves the lower bound in probability. By recurrence the walk returns to $o$ infinitely often, so the instantaneous logarithmic displacement cannot converge almost surely to $1/3$.</p>

## The range of the walk {#section-pathwise-range}

<p>Write $W_n=\{X_0,\ldots,X_n\}$ for the visited vertices and $A_n=\sum_{y\in W_n}\pi(y)$ for their degree mass. The distinction matters on graphs with unbounded degrees.</p>

<a id="tag-YIJB" data-assertion="theorem" data-title="Quadratic volume and linear resistance give degree-range exponent two thirds"></a>
<p>Under the deterministic hypotheses of NNW7,</p>
<div class="math-display">$$\lim_{n\to\infty}\frac{\log A_n}{\log n}=\frac23
\qquad\mathbf P_o\text{-almost surely}.$$</div>
<p>If the graph has a finite maximum degree, then also</p>
<div class="math-display">$$\lim_{n\to\infty}\frac{\log|W_n|}{\log n}=\frac23
\qquad\mathbf P_o\text{-almost surely}.$$</div>
<p><em>Proof.</em> Since $W_n\subseteq B(L_n)$, the upper bound follows from $A_n\le V(L_n)$ and 7WII.</p>
<p>For the lower bound, fix $0<\eta<1$, take $r_j=2^j$ and put $s_j=\lfloor r_j^{1-\eta}\rfloor$. Eventually $s_j\le\mathcal R(r_j)/2$. The degree mass in $B(s_j)$ missed before $T_{r_j}$ is</p>
<div class="math-display">$$Z_j=\sum_{y\in B(s_j)}\pi(y)\mathbf1_{\{T_y>T_{r_j}\}}.$$</div>
<p>LCUN and Markov's inequality give</p>
<div class="math-display">$$\mathbf P_o\bigl(Z_j\ge V(s_j)/2\bigr)
\le\frac{2s_j}{\mathcal R(r_j)-s_j}
\le\frac{4s_j}{\mathcal R(r_j)}
=r_j^{-\eta+o(1)}.$$</div>
<p>The series in $j$ converges. Therefore, almost surely, for all sufficiently large $j$,</p>
<div class="math-display">$$A_{T_{r_j}}\ge\frac12V(s_j)
=r_j^{2(1-\eta)+o(1)}.$$</div>
<p>For any fixed $\delta>0$, 7WII also gives $T_{r_j}\le r_j^{3+\delta}$ eventually. Choose $j$ with $r_j^{3+\delta}\le n<r_{j+1}^{3+\delta}$. Monotonicity of $A_n$ yields</p>
<div class="math-display">$$\liminf_{n\to\infty}\frac{\log A_n}{\log n}
\ge\frac{2(1-\eta)}{3+\delta}.$$</div>
<p>Intersect the full-probability events for a countable sequence of pairs $\eta,\delta$ tending to zero. This proves the degree-range limit. If $\pi(y)\le\Delta<\infty$ everywhere, then $|W_n|\le A_n\le\Delta|W_n|$, giving the cardinality assertion. No independence between the events of missing different vertices is needed.</p>

## Pathwise consequences for the incipient limits {#section-iic-paths}

<a id="tag-HJKG" data-assertion="theorem" data-title="Finite-triangle incipient limits have pathwise exit, maximal-distance and range exponents"></a>
<p>Let $\mu$ be either of the cylinder limits specified in IXCJ, with finite critical triangle and, for distant-point conditioning, the stated fixed-shift ratio hypothesis. For $\mu$-almost every configuration $\omega$, ordinary simple random walk on the open root cluster satisfies</p>
<div class="math-display">$$\lim_{r\to\infty}\frac{\log T_r}{\log r}=3,\qquad
\lim_{n\to\infty}\frac{\log(1+L_n)}{\log n}=\frac13,\qquad
\lim_{n\to\infty}\frac{\log|W_n|}{\log n}=\frac23
\quad\mathbf P_0^\omega\text{-almost surely}.$$</div>
<p>On each such fixed cluster, $\log(1+d_\omega(0,X_n))/\log n$ converges to $1/3$ in walk probability. The same assertions hold for the lazy walk.</p>
<p><em>Proof.</em> As in IXCJ, RG3Z and POD2 give degree-volume exponent two and resistance exponent one on a common set of full $\mu$ measure. Apply 7WII and YIJB to each of those fixed graphs. The cluster degree is at most $2d$, so the degree-range result gives the number of visited vertices. For the lazy walk, couple it to the ordinary path through an independent Bernoulli clock. The number of ordinary jumps by time $n$, divided by $n$, tends almost surely to $1/2$; equivalently, the time of the $k$th jump divided by $k$ tends to two. This preserves all three pathwise exponents. Conditioning on that clock also transfers the fixed-time convergence in probability, since its time index is eventually between $n/4$ and $3n/4$ with probability tending to one.</p>
<p>These are quenched statements: first choose a cluster in the full-measure set, then sample a walk on it. They complete the pathwise exit-time, maximum-distance and range tasks left separate above. They do not identify different IIC constructions or give annealed heat-kernel asymptotics. In particular, maximum distance, position at a fixed time and the number of visited vertices are three different observables.</p>


## Averaging the return bound {#section-annealed-upper}

<p>Almost-sure logarithmic exponents do not by themselves control averages over clusters. We now let the rooted graph be random, with law $\mu$, and write $\mathbb E_\mu$ for environment expectation. Assume a measurable family of infinite connected locally finite simple graphs with unit conductances; retain the degree-volume and kernel conventions above. All probabilities inside $\mathbb E_\mu$ concern the walk on the fixed graph.</p>

<a id="tag-VFZN" data-assertion="theorem" data-title="A linear lower-volume tail gives an integrable tail for the rescaled return kernel"></a>
<p>Suppose that, for some $a\ge1$, every integer $r\ge1$ and $0<\varepsilon<1$ satisfy</p>
<div class="math-display">$$\mu\bigl(V(r)\le\varepsilon r^2\bigr)\le a\varepsilon.$$</div>
<p>Then there is $C<\infty$, depending only on $a$, such that for $n\ge1$ and $\lambda>0$,</p>
<div class="math-display">$$\mu\bigl((n+1)^{2/3}\widehat q_n(o,o)>\lambda\bigr)
\le\min\{1,C\lambda^{-3}\}.$$</div>
<p>Consequently, for each $0<p<3$,</p>
<div class="math-display">$$\mathbb E_\mu[\widehat q_n(o,o)^p]
\le C_p(n+1)^{-2p/3},\qquad
\mathbb E_\mu[q_{2n}(o,o)^p]\le C_p(n+1)^{-2p/3}.$$</div>
<p><em>Proof.</em> The assumed volume bound also holds for $\varepsilon\ge1$, since $a\ge1$. Fix $t>0$ with $(n+1)t\ge8$, and choose $r=\lfloor(n+1)t/4\rfloor$. Then $r\ge(n+1)t/8$ and $2r/(n+1)\le t/2$. KGNK shows that $\widehat q_n(o,o)>t$ forces $V(r)<4/t$. Hence</p>
<div class="math-display">$$\mu\bigl(\widehat q_n(o,o)>t\bigr)
\le\frac{4a}{tr^2}
\le\frac{256a}{(n+1)^2t^3}.$$</div>
<p>If $(n+1)t<8$, the same bound with $C=512\max\{1,a\}$ in place of $256a$ is at least one, so it remains valid. Substitute $t=\lambda(n+1)^{-2/3}$. For $U=(n+1)^{2/3}\widehat q_n(o,o)$, Tonelli gives</p>
<div class="math-display">$$\mathbb E_\mu U^p
=p\int_0^\infty\lambda^{p-1}\mu(U>\lambda)\,d\lambda
\le1+\frac{Cp}{3-p}.$$</div>
<p>The binomial comparison $q_{2n}(o,o)\le2\widehat q_{2n}(o,o)$ from NNW7 gives the ordinary-walk bound. Its proof uses only the spectral representation, so no geometric exponent hypothesis is needed here.</p>
<p>The radius was chosen after the threshold $t$. At a fixed radius the stated lower-volume tail alone does not give $\mathbb E_\mu[V(r)^{-1}]=O(r^{-2})$; integrating that tail directly can lose a logarithm. The argument above avoids that additional assumption.</p>

## Two-sided annealed estimates {#section-annealed-two-sided}

<a id="tag-Z0P0" data-assertion="theorem" data-title="Volume moments and resistance tails give two-sided annealed return and mean-exit bounds"></a>
<p>In addition to VFZN's lower-volume hypothesis, suppose that for constants $b,c_R,\beta>0$ and an integer $r_0\ge1$,</p>
<div class="math-display">$$\mathbb E_\mu V(r)\le br^2\quad(r\ge1),\qquad
\mu\bigl(\mathcal R(r)\le r/\lambda\bigr)
\le c_R\lambda^{-\beta}\quad(r\ge r_0,\ \lambda>1).$$</div>
<p>There are constants $c,C>0$ and $r_*<\infty$ such that</p>
<div class="math-display">$$cr^3\le\mathbb E_\mu\mathbf E_o T_r\le Cr^3
\qquad(r\ge r_*).$$</div>
<p>For every $0<p<3$ there are $c_p,C_p>0$ and $n_*<\infty$ such that, for $n\ge n_*$,</p>
<div class="math-display">$$\begin{aligned}
c_p n^{-2p/3}&\le\mathbb E_\mu[\widehat q_n(o,o)^p]\le C_p n^{-2p/3},\\
c_p n^{-2p/3}&\le\mathbb E_\mu[q_{2n}(o,o)^p]\le C_p n^{-2p/3}.
\end{aligned}$$</div>
<p><em>Proof.</em> Choose $L>1$, $B>0$ and $0<\varepsilon<1$ so that $c_RL^{-\beta}\le1/8$, $b/B\le1/8$ and $a\varepsilon\le1/8$. For $r\ge\max\{r_0,8L\}$ put $s=\lfloor r/(4L)\rfloor$ and consider</p>
<div class="math-display">$$F_r=\{\mathcal R(r)>r/L,\quad V(r)\le Br^2,\quad V(s)>\varepsilon s^2\}.$$</div>
<p>The union bound and Markov's inequality give $\mu(F_r)\ge5/8$. On this event $s\ge r/(8L)$ and $s\le\lfloor\mathcal R(r)/4\rfloor$. With $m(r)=\mathbf E_oT_r$ and $m_*(r)=\sup_{x\in D_r}\mathbf E_xT_r$, 331W therefore gives</p>
<div class="math-display">$$m(r)\ge\frac{\varepsilon}{128L^3}r^3=:c_0r^3,
\qquad m_*(r)\le2Br^3=:C_0r^3.$$</div>
<p>Averaging the first inequality over $F_r$ proves the lower mean-exit bound. The upper bound follows directly from $m(r)\le rV(r-1)\le rV(r)$ and the first-moment hypothesis.</p>
<p>For large $n$, take $r=\lceil(n/c_0)^{1/3}\rceil$, so $F_r$ is available. On $F_r$, the lazy means satisfy $u_r=2m(r)\ge2n$ and $M_r=2m_*(r)\le2C_0r^3$. The lower bound in KGNK yields</p>
<div class="math-display">$$\widehat q_{2n}(o,o)
\ge\frac{c_0^2r^6}{4C_0^2r^6\,Br^2}
\ge c_1n^{-2/3}.$$</div>
<p>This event has probability at least $5/8$, uniformly in large $n$. The lazy diagonal kernel is nonincreasing, so it gives the same lower bound for $\widehat q_n$. Apply the argument also at $4n$. The other binomial comparison from NNW7, using $\pi(o)\ge1$, gives</p>
<div class="math-display">$$q_{2n}(o,o)\ge\widehat q_{8n}(o,o)
-\left(\frac{256}{729}\right)^n.$$</div>
<p>For all sufficiently large $n$ the exponential term is at most half the polynomial lower bound. Thus each kernel exceeds a fixed positive multiple of $n^{-2/3}$ on an event of probability at least $5/8$. Raising to any positive power and averaging proves the lower moment bounds; VFZN supplies the upper bounds for $p<3$. Neither independence between the three conditions defining $F_r$ nor convergence of the rescaled kernels is used.</p>

## Mean intrinsic displacement {#section-annealed-displacement}

<a id="tag-5QU6" data-assertion="theorem" data-title="The annealed return bound controls small intrinsic displacement and its mean lower bound"></a>
<p>Assume VFZN's lower-volume bound and $\mathbb E_\mu V(r)\le br^2$ for $r\ge1$. Under the joint law that first chooses the graph and then runs ordinary walk from its root,</p>
<div class="math-display">$$\mathbb E_\mu\mathbf P_o\bigl(d_G(o,X_n)\le s\bigr)
\le\min\{1,C(s+1)(n+1)^{-1/3}\}
\qquad(n\ge1,\ s\in\mathbb Z_{\ge0}).$$</div>
<p>In particular, for all sufficiently large $n$,</p>
<div class="math-display">$$\mathbb E_\mu\mathbf E_o d_G(o,X_n)\ge c n^{1/3}.$$</div>
<p>The same conclusions hold for the lazy walk. No resistance hypothesis is needed for these lower bounds on dispersion.</p>
<p><em>Proof.</em> Reversibility and Cauchy–Schwarz on each fixed graph give</p>
<div class="math-display">$$\mathbf P_o(X_n\in B(s))\le\sqrt{V(s)q_{2n}(o,o)}.$$</div>
<p>A second application of Cauchy–Schwarz, now in the environment, bounds its expectation by</p>
<div class="math-display">$$\sqrt{\mathbb E_\mu V(s)\,\mathbb E_\mu q_{2n}(o,o)}
\le C(s+1)(n+1)^{-1/3}.$$</div>
<p>For $s=0$ use $V(0)\le V(1)$; for $s\ge1$ use the assumed first moment. VFZN with $p=1$ supplies the kernel estimate. Choose a fixed small $\eta>0$ and then $s=\lfloor\eta(n+1)^{1/3}\rfloor$. For sufficiently large $n$, the displayed probability is at most $1/2$ and $s\ge(\eta/2)(n+1)^{1/3}$. The mean distance is consequently at least $s/2$. Replacing $q$ by $\widehat q$ gives the identical lazy-walk proof.</p>
<p>This is a lower bound on the mean. The previous almost-sure maximum-distance exponent does not supply a matching upper mean bound without additional control of its tail.</p>

## Annealed bounds for the incipient limits {#section-iic-annealed}

<a id="tag-G85Z" data-assertion="theorem" data-title="Finite-triangle incipient limits have two-sided annealed return and mean-exit bounds"></a>
<p>Let $\mu$ be either of the incipient cylinder limits in IXCJ, with finite critical triangle and the stated ratio hypothesis in the distant-point case. There are $c,C>0$ such that, for every integer $r,n\ge1$,</p>
<div class="math-display">$$cr^3\le\mathbb E_\mu\mathbf E_0^\omega T_r\le Cr^3,
\qquad
cn^{-2/3}\le\mathbb E_\mu\mathbf P_0^\omega(X_{2n}=0)\le Cn^{-2/3}.$$</div>
<p>More generally, for each $0<p<3$ the $p$th environment moment of this ordinary return probability is bounded above and below by positive multiples of $n^{-2p/3}$. For the lazy walk, the same return bounds hold at every time $n$, and mean exit times are doubled. Both walks satisfy the small-displacement bound of 5QU6 and its lower bound of order $n^{1/3}$ on mean intrinsic distance.</p>
<p><em>Proof.</em> Every cluster degree lies between one and $2d$. Thus the cardinality lower tail in RG3Z implies VFZN with $a=4K$, while the first moment in KIGU, with the critical ball bound used in Z78U, gives</p>
<div class="math-display">$$\mathbb E_\mu V(r)
\le2dA^2(r+1)^2\le8dA^2r^2\qquad(r\ge1).$$</div>
<p>POD2 supplies the resistance tail with $\beta=1/2$ and $r_0=8$. Apply Z0P0 and 5QU6. Multiplying the normalized return kernel by $\pi(0)\in[1,2d]$ preserves the two-sided moment bounds. For the finitely many smaller radii, $T_r\ge r$ and the already proved upper bound absorb the lower constant. At the finitely many smaller times an ordinary walk can alternate along one incident edge, with probability at least $(2d)^{-2n}$; a lazy walk can stay at the root, with probability $2^{-n}$. These positive uniform bounds extend the return estimates to all $n\ge1$.</p>
<p>These are annealed two-sided bounds, stronger than an averaged logarithmic exponent but not asymptotic equivalents with a limiting constant. They add neither IIC uniqueness nor identification of the two constructions. The probabilistic lower-volume tail is used directly; no inverse-volume moment is asserted or required.</p>


## Quantitative escape tails {#section-annealed-escape-tail}

<p>Write $\overline{\mathbf P}=\mu(d\omega)\mathbf P_o^\omega$ and $\overline{\mathbf E}$ for the joint law and expectation of the environment and the walk. We keep the hypotheses of Z0P0: a linear lower-volume tail, $\mathbb E_\mu V(r)\le br^2$, and a lower-resistance tail with exponent $\beta>0$. Put</p>
<div class="math-display">$$\gamma=\min\{1,\beta\},\qquad
\delta=\frac{3\gamma}{22+3\gamma},\qquad
\alpha=\frac{\delta}{3}=\frac{\gamma}{22+3\gamma}.$$</div>

<a id="tag-C2KR" data-assertion="theorem" data-title="Volume and resistance tails give quantitative bounds on fast intrinsic escape"></a>
<p>There is $C<\infty$, depending only on the constants in Z0P0, such that</p>
<div class="math-display">$$\overline{\mathbf P}(L_n\ge\lambda n^{1/3})
\le\min\{1,C\lambda^{-\delta}\}
\qquad(n\ge1,\ \lambda\ge1).$$</div>
<p>Equivalently, the following fast-exit bound holds for integers $r\ge1$ and real $t\ge0$:</p>
<div class="math-display">$$\overline{\mathbf P}(T_r\le t)
\le\min\left\{1,C\left(\frac{t}{r^3}\right)^\alpha\right\}.$$</div>
<p>The same bounds hold for the lazy walk's maximum distance and exit time.</p>
<p><em>Proof.</em> Fix $n\ge1$ and a large $\lambda$. Choose</p>
<div class="math-display">$$h=\lambda^{3/(22+3\gamma)},\qquad
u=\lceil(hn)^{1/3}\rceil,\qquad
s=\lceil4hu\rceil,\qquad
r=\lceil\lambda n^{1/3}\rceil.$$</div>
<p>Since $u\le2(hn)^{1/3}$ and $s\le5hu$, a fixed lower bound on $\lambda$, independent of $n$, ensures $r_0\le s<r$. Consider the environment event</p>
<div class="math-display">$$F=\{\mathcal R(r)>r/h,\quad\mathcal R(s)>s/h,
\quad V(u)>u^2/h,\quad V(s)\le hs^2\}.$$</div>
<p>The three distributional assumptions and a union bound give</p>
<div class="math-display">$$\mu(F^c)\le(a+b)h^{-1}+2c_Rh^{-\beta}
\le C_1h^{-\gamma}.$$</div>
<p>On $F$, $\lfloor\mathcal R(s)/4\rfloor\ge u$. The Green-function bounds 331W, with ordinary mean exit times $m(s)$ and $m_*(s)$ as in 7WII, give</p>
<div class="math-display">$$m(s)\ge\frac{s u^2}{2h^2}\ge\frac{2u^3}{h}\ge2n,
\qquad m_*(s)\le2hs^3,
\qquad\frac{m_*(s)}{m(s)}\le100h^5.$$</div>
<p>Apply the return-through-root inequality (*) from the proof of 7WII. That inequality requires only $s<r$ and $n<m(s)$, not the geometric exponent limits used later in that proof. On $F$ it yields</p>
<div class="math-display">$$\mathbf P_o(T_r\le n)
\le\frac{s\,m_*(s)}{\mathcal R(r)(m(s)-n)}
\le\frac{200s h^6}{r}
\le\frac{2000h^{22/3}}{\lambda}.$$</div>
<p>Now average over $F$ and its complement. Since $\{L_n\ge\lambda n^{1/3}\}=\{T_r\le n\}$,</p>
<div class="math-display">$$\overline{\mathbf P}(L_n\ge\lambda n^{1/3})
\le C_1h^{-\gamma}+2000h^{22/3}\lambda^{-1}
\le C_2\lambda^{-\delta}.$$</div>
<p>The choice of $h$ balances the two powers. Increasing $C_2$ covers the remaining bounded interval of $\lambda\ge1$. This gives a bound uniform in every $n\ge1$, including times too small for asymptotic geometric estimates.</p>
<p>For the exit formulation, put $k=\lfloor t\rfloor$. If $k=0$ the event is empty. Otherwise use $\{T_r\le k\}=\{L_k\ge r\}$ with $\lambda=r/k^{1/3}$. When $\lambda<1$ the stated upper bound is trivial; when $\lambda\ge1$ the first estimate gives $C(k/r^3)^\alpha\le C(t/r^3)^\alpha$. Finally couple the lazy walk to the ordinary path by inserting independent holding times. Its maximum by time $n$ is no greater than $L_n$, and its exit time is at least $T_r$, so both inequalities transfer.</p>

## Displacement and exit-time moments {#section-annealed-walk-moments}

<p>The added one in the displacement variables below is essential for negative moments: the walk returns to the root, and on a bipartite graph these returns occur at even times.</p>

<a id="tag-J75E" data-assertion="theorem" data-title="The scaled intrinsic displacement, maximum and exit time have two-sided fractional moment bounds"></a>
<p>Under the hypotheses and with the exponents of C2KR, both families</p>
<div class="math-display">$$\mathsf{D}_n=\frac{1+d_G(o,X_n)}{n^{1/3}},\qquad
\mathsf{M}_n=\frac{1+L_n}{n^{1/3}}\qquad(n\ge1)$$</div>
<p>are uniformly tight and uniformly bounded away from zero in joint probability. More precisely, for $Z_n=\mathsf{D}_n$ or $\mathsf{M}_n$,</p>
<div class="math-display">$$\overline{\mathbf P}(Z_n\le\varepsilon)\le C\varepsilon
\quad(0<\varepsilon\le1),\qquad
\overline{\mathbf P}(Z_n>\lambda)\le C\lambda^{-\delta}
\quad(\lambda\ge1).$$</div>
<p>For every $-1<p<\delta$ there are constants $0<c_p\le C_p<\infty$ such that</p>
<div class="math-display">$$c_p\le\overline{\mathbf E}\mathsf{D}_n^p\le C_p,
\qquad c_p\le\overline{\mathbf E}\mathsf{M}_n^p\le C_p
\qquad(n\ge1).$$</div>
<p>For exit times, for every $-\alpha<p\le1$ there are positive finite constants such that</p>
<div class="math-display">$$c_p r^{3p}\le\overline{\mathbf E}T_r^p\le C_p r^{3p}
\qquad(r\ge1).$$</div>
<p>All these assertions also hold for the lazy walk, with its own position, maximum and exit time.</p>
<p><em>Proof.</em> If $\varepsilon n^{1/3}<1$, the event $\mathsf{D}_n\le\varepsilon$ is empty. Otherwise set $j=\lfloor\varepsilon n^{1/3}-1\rfloor$. By 5QU6,</p>
<div class="math-display">$$\overline{\mathbf P}(\mathsf{D}_n\le\varepsilon)
\le C(j+1)(n+1)^{-1/3}\le C\varepsilon.$$</div>
<p>Since $\mathsf{M}_n\ge \mathsf{D}_n$, the same lower tail holds for $\mathsf{M}_n$. For $\lambda\ge2$, $\mathsf{M}_n>\lambda$ implies $L_n>(\lambda/2)n^{1/3}$. C2KR therefore gives the upper tail; enlarge its constant for $1\le\lambda<2$. It also bounds $\mathsf{D}_n$ because $\mathsf{D}_n\le \mathsf{M}_n$.</p>
<p>For $0<p<\delta$, integrate the upper tail:</p>
<div class="math-display">$$\overline{\mathbf E}Z_n^p
=p\int_0^\infty x^{p-1}\overline{\mathbf P}(Z_n>x)\,dx
\le1+\frac{Cp}{\delta-p}.$$</div>
<p>For $p=-q$ with $0<q<1$, apply the same identity to $Z_n^{-1}$. Its upper tail is at most $C/x$ for $x\ge1$, giving $\overline{\mathbf E}Z_n^{-q}\le1+Cq/(1-q)$. To obtain the lower moment bounds, choose fixed $0<\ell<H<\infty$ so that the two tail estimates put probability at least $1/2$ in $[\ell,H]$, uniformly in $n$. Then</p>
<div class="math-display">$$\overline{\mathbf E}Z_n^p\ge\tfrac12\min\{\ell^p,H^p\}>0.$$</div>
<p>The case $p=0$ is immediate.</p>
<p>For $U_r=T_r/r^3$, C2KR gives $\overline{\mathbf P}(U_r\le\varepsilon)\le C\varepsilon^\alpha$. Also 331W and the volume first moment give $\overline{\mathbf E}U_r\le b$ for every $r\ge1$. Jensen's inequality gives the upper bound for $0<p\le1$; integrating the lower tail gives it for $-\alpha<p<0$. The small-value bound and Markov's inequality put at least half the mass of $U_r$ in a fixed compact subinterval of $(0,\infty)$, giving the lower bounds as above. Since $T_r\ge r>0$, every negative power is well defined. The lazy version uses the same small-value estimates, 5QU6 for its position, and $\overline{\mathbf E}\widehat T_r=2\overline{\mathbf E}T_r$.</p>
<p>The endpoint moment orders are excluded where the tail integral diverges. These ranges are sufficient conditions from the displayed estimates; no optimality or divergence at an excluded endpoint is asserted. In particular $\delta<1$, so the result does not give an upper bound of order $n^{1/3}$ for mean displacement.</p>

## Quantitative tightness on the incipient limits {#section-iic-tightness}

<a id="tag-YWT9" data-assertion="theorem" data-title="Finite-triangle incipient limits have quantitative intrinsic-walk tightness and fractional moments"></a>
<p>Let $\mu$ be either of the incipient limits in IXCJ, with finite critical triangle and the stated ratio hypothesis for distant-point conditioning. Under the joint environment and walk law, for $n,r\ge1$, $\lambda\ge1$ and $t\ge0$,</p>
<div class="math-display">$$\overline{\mathbf P}(L_n\ge\lambda n^{1/3})
\le\min\{1,C\lambda^{-3/47}\},\qquad
\overline{\mathbf P}(T_r\le t)
\le\min\{1,C(t/r^3)^{1/47}\}.$$</div>
<p>The scaled position $(1+d_\omega(0,X_n))/n^{1/3}$, scaled maximum $(1+L_n)/n^{1/3}$ and scaled exit time $T_r/r^3$ are uniformly tight and bounded away from zero. Their moment bounds include</p>
<div class="math-display">$$\begin{aligned}
\overline{\mathbf E}(1+d_\omega(0,X_n))^p&\asymp n^{p/3},\quad
\overline{\mathbf E}(1+L_n)^p\asymp n^{p/3}
&&(-1<p<3/47),\\
\overline{\mathbf E}T_r^p&\asymp r^{3p}
&&(-1/47<p\le1).
\end{aligned}$$</div>
<p>Here the positive comparison constants may depend on the model and the fixed moment order, but not on $n$ or $r$. The conclusions hold for ordinary and lazy walk.</p>
<p><em>Proof.</em> G85Z checks the volume hypotheses and POD2's resistance tail for these incipient limits, with $\beta=1/2$. Thus $\gamma=1/2$, $\delta=3/47$ and $\alpha=1/47$. Apply C2KR and J75E. For the scaled exit time, its small-value bound comes from C2KR and its large-value bound from the cubic annealed mean estimate. No uniqueness of the incipient limit or identification of its constructions is used.</p>
<p>This supplies control at the scale itself, beyond the logarithmic exponents proved earlier. The power $3/47$ is a consequence of balancing the two estimates in this proof, not a claimed sharp tail exponent. A matching upper bound on mean intrinsic displacement remains separate.</p>


## Quantitative bounds for the range {#section-range-tails}

<p>Retain Z0P0's random-graph hypotheses and the joint law $\overline{\mathbf P}$. As above, $W_n=\{X_0,\ldots,X_n\}$ and $A_n=\sum_{y\in W_n}\pi(y)$ is the degree mass of the visited set. Put</p>
<div class="math-display">$$\kappa=\frac{3\beta}{11\beta+6},\qquad
\eta=\frac{\delta}{2+\delta},$$</div>
<p>where $\beta$ is the resistance-tail exponent and $\delta$ is the escape exponent in C2KR.</p>

<a id="tag-JC9J" data-assertion="theorem" data-title="Volume and resistance tails give two-sided probability and fractional moment bounds for degree range"></a>
<p>There is $C<\infty$ such that, uniformly in integers $n\ge1$,</p>
<div class="math-display">$$\overline{\mathbf P}(A_n\le\varepsilon n^{2/3})\le C\varepsilon^\kappa
\quad(0<\varepsilon\le1),\qquad
\overline{\mathbf P}(A_n>\lambda n^{2/3})\le C\lambda^{-\eta}
\quad(\lambda\ge1).$$</div>
<p>Thus $A_n/n^{2/3}$ is uniformly tight and bounded away from zero. For every $-\kappa<p<\eta$,</p>
<div class="math-display">$$c_p n^{2p/3}\le\overline{\mathbf E}A_n^p\le C_p n^{2p/3}
\qquad(n\ge1),$$</div>
<p>with $0<c_p\le C_p<\infty$. There is also a lower bound $\overline{\mathbf E}A_n\ge c n^{2/3}$. The same assertions hold for the lazy walk's degree range. No degree bound is assumed here.</p>
<p><em>Proof.</em> The upper tail follows from $A_n\le V(L_n)$. For large $\lambda$, set $r=\lfloor n^{1/3}\lambda^{1/(2+\delta)}\rfloor$. Then C2KR and the volume first moment give</p>
<div class="math-display">$$\begin{aligned}
\overline{\mathbf P}(A_n>\lambda n^{2/3})
&\le\overline{\mathbf P}(L_n>r)+\mu(V(r)>\lambda n^{2/3})\\
&\le C\lambda^{-\delta/(2+\delta)}+b\lambda^{2/(2+\delta)-1}.
\end{aligned}$$</div>
<p>Here $r\ge n^{1/3}\lambda^{1/(2+\delta)}/2$; increasing $C$ covers the remaining bounded values of $\lambda$.</p>
<p>For the lower tail, write $k=\kappa^{-1}=11/3+2/\beta$ and take small $\varepsilon>0$. If $\varepsilon n^{2/3}<1$, the event is empty since $A_n\ge\pi(o)\ge1$. Otherwise choose</p>
<div class="math-display">$$h=(1024\varepsilon)^{-1/k},\qquad
r=\lfloor n^{1/3}h^{-1/3}\rfloor,\qquad
s=\left\lfloor\frac{r}{4h^{1+1/\beta}}\right\rfloor.$$</div>
<p>The nonempty-event case gives $n^{1/3}\ge32h^{k/2}$. Consequently, once $h$ exceeds a fixed constant, $r\ge r_0$, $1\le s<r$, and</p>
<div class="math-display">$$r\ge\tfrac12 n^{1/3}h^{-1/3},\qquad
s\ge\frac{r}{8h^{1+1/\beta}}
\ge\frac{n^{1/3}}{16h^{4/3+1/\beta}}.$$</div>
<p>In particular these choices use the resistance hypothesis only in its stated radius range. Let</p>
<div class="math-display">$$F=\{\mathcal R(r)>r/h^{1/\beta},\quad V(s)>s^2/h\}.
\qquad \mu(F^c)\le(c_R+a)/h.$$</div>
<p>On $F$ we have $s/\mathcal R(r)\le1/(4h)$. Let $M$ be the degree mass in $B(s)$ not visited before $T_r$. Summing LCUN's hitting bound over this ball and applying Markov's inequality gives, on each such environment,</p>
<div class="math-display">$$\mathbf P_o(M\ge V(s)/2)
\le\frac{2s}{\mathcal R(r)-s}\le h^{-1}.$$</div>
<p>This step does not require independence among the events of missing individual vertices. Also 331W and the volume first moment imply</p>
<div class="math-display">$$\overline{\mathbf P}(T_r>n)
\le\frac{\overline{\mathbf E}T_r}{n}
\le\frac{br^3}{n}\le\frac b h.$$</div>
<p>If $F$ holds, $M<V(s)/2$ and $T_r\le n$, the visited mass satisfies</p>
<div class="math-display">$$A_n\ge A_{T_r}\ge V(s)-M
>\frac{s^2}{2h}\ge\frac{n^{2/3}}{512h^k}
=2\varepsilon n^{2/3}.$$</div>
<p>The three exceptional probabilities are therefore at most $C/h=C(1024\varepsilon)^\kappa$. Increasing the constant covers the remaining $\varepsilon\in(0,1]$. For the lazy walk, the visited set at exit is unchanged by the holding times, while its mean exit time is doubled. Its range at a fixed time is contained in the ordinary range under the same coupling. These facts give both tails for that walk as well.</p>
<p>Integrating the upper tail of $A_n/n^{2/3}$ gives the moment bound for $0<p<\eta$; integrating the upper tail of its reciprocal gives the bound for $-\kappa<p<0$. The two probability bounds place at least half the mass in a fixed compact subinterval of $(0,\infty)$, giving the lower moment bounds and the stated first-moment lower bound. At $p=0$ the assertion is immediate. No added one is needed: the range already contains the root.</p>

## Range bounds with an exponential volume tail {#section-range-volume-tail}

<a id="tag-E3IN" data-assertion="theorem" data-title="An exponential upper-volume tail improves the positive fractional moments of degree range"></a>
<p>In addition to the hypotheses of JC9J, suppose that for some $c_V,C_V>0$,</p>
<div class="math-display">$$\mu(V(r)>u r^2)\le C_Ve^{-c_Vu}
\qquad(r\ge1,\ u\ge1).$$</div>
<p>Then, for $n\ge1$ and $\lambda\ge2$,</p>
<div class="math-display">$$\overline{\mathbf P}(A_n>\lambda n^{2/3})
\le C\left(\frac{\log\lambda}{\lambda}\right)^{\delta/2}.$$</div>
<p>Consequently the two-sided degree-range moment bounds hold throughout the larger range</p>
<div class="math-display">$$c_p n^{2p/3}\le\overline{\mathbf E}A_n^p\le C_p n^{2p/3}
\qquad(-\kappa<p<\delta/2).$$</div>
<p>Both conclusions hold for ordinary and lazy walk.</p>
<p><em>Proof.</em> Fix $K\ge\max\{1,c_V^{-1}\}$ and, for large $\lambda$, take</p>
<div class="math-display">$$r=\left\lfloor n^{1/3}\sqrt{\frac{\lambda}{K\log\lambda}}\right\rfloor.$$</div>
<p>A fixed lower bound on $\lambda$, independent of $n$, ensures that $r$ is at least half the quantity inside the floor and $r/n^{1/3}\ge1$. Splitting according to $L_n>r$ as before, the escape term is at most $C(\log\lambda/\lambda)^{\delta/2}$. The volume term is at most</p>
<div class="math-display">$$C_V\exp\!\left(-c_V\frac{\lambda n^{2/3}}{r^2}\right)
\le C_V\lambda^{-c_VK}\le C_V\lambda^{-1}.$$</div>
<p>Since $0<\delta<1$, this is absorbed into the claimed tail; bounded $\lambda\ge2$ are covered by changing the constant. For $0<p<\delta/2$, the tail integral converges because</p>
<div class="math-display">$$\int_2^\infty x^{p-1-\delta/2}(\log x)^{\delta/2}\,dx<\infty.$$</div>
<p>The inverse moments and all lower bounds remain those of JC9J. The argument uses the corresponding maximum bound for either walk.</p>

## Quantitative range on the incipient limits {#section-iic-range-moments}

<a id="tag-PSNV" data-assertion="theorem" data-title="Finite-triangle incipient limits have quantitative range tightness and two-sided fractional moments"></a>
<p>Let $\mu$ be either of the incipient limits in IXCJ, with finite critical triangle and, for distant-point conditioning, the stated fixed-shift ratio hypothesis. For ordinary or lazy walk, let $N_n=|W_n|$ be the number of visited vertices, including the root. Uniformly in $n\ge1$,</p>
<div class="math-display">$$\overline{\mathbf P}(N_n\le\varepsilon n^{2/3})\le C\varepsilon^{3/23}
\quad(0<\varepsilon\le1),\qquad
\overline{\mathbf P}(N_n>\lambda n^{2/3})
\le C\left(\frac{\log\lambda}{\lambda}\right)^{3/94}
\quad(\lambda\ge2).$$</div>
<p>Thus $N_n/n^{2/3}$ is uniformly tight and bounded away from zero, and</p>
<div class="math-display">$$\overline{\mathbf E}N_n^p\asymp n^{2p/3}
\qquad(-3/23<p<3/94),\qquad
\overline{\mathbf E}N_n\ge c n^{2/3}.$$</div>
<p>The same bounds hold for degree range $A_n$. Constants may depend on the model and, for moments, the fixed power, but not on time.</p>
<p><em>Proof.</em> G85Z supplies the hypotheses of Z0P0 with $\beta=1/2$, so $\kappa=3/23$ and $\delta/2=3/94$. Since $V(r)\le2d|B(r)|$, Z78U gives, with its constant $A$,</p>
<div class="math-display">$$\mu(V(r)>u r^2)
\le\sqrt2\exp\!\left(-\frac{u}{32dA^2}\right)
\qquad(r\ge1,\ u\ge1),$$</div>
<p>using $(r+1)^2\le4r^2$. Apply JC9J and E3IN. Finally $N_n\le A_n\le2dN_n$, so the probability and moment bounds transfer to vertex cardinality. For negative powers this comparison reverses direction, but only changes the constants.</p>
<p>These are bounds at the $n^{2/3}$ scale under the joint environment-and-walk law. They complement HJKG's almost-sure logarithmic range exponent; they do not assert convergence of the normalized range, sharp tail powers, divergence at the excluded moment endpoints, or an upper first-moment bound of order $n^{2/3}$. No identification of incipient constructions is used.</p>



## Slow exit and all positive moments {#section-slow-exit-moments}

<p>An exponential upper tail for volume gives more than a first mean-exit bound. On a fixed graph, the supremum of the mean exit time controls the chance of surviving each successive time block. Averaging this geometric bound over the volume yields a stretched-exponential tail.</p>

<a id="tag-VI2M" data-assertion="theorem" data-title="An exponential volume tail gives a square-root exponential exit tail and all positive exit-time moments"></a>
<p>Let $\mu$ be a law on the infinite connected locally finite rooted graphs considered above. Suppose that for some $c_V,C_V&gt;0$,</p>
<div class="math-display">$$
\mu(V(r)&gt;u r^2)\le C_Ve^{-c_Vu}
\qquad(r\ge1,\ u\ge1).
$$</div>
<p>For ordinary or lazy walk there are $c,C,\varepsilon&gt;0$, independent of $r$, such that</p>
<div class="math-display">$$
\overline{\mathbf P}(T_r&gt;t r^3)\le Ce^{-c\sqrt t}
\qquad(r\ge1,\ t\ge1),
$$</div>
<div class="math-display">$$
\sup_{r\ge1}\overline{\mathbf E}
\exp\!\left[\varepsilon\left(
\sqrt{T_r/r^3}+V(r)/r^2\right)\right]&lt;\infty.
$$</div>
<p>For every real $q&gt;0$, $\overline{\mathbf E}T_r^q\le C_qr^{3q}$. More precisely, $\|T_r/r^3\|_q\le Cq^2$ for $q\ge1$. For the lazy walk, $T_r$ in these formulas means its own exit time. No resistance or lower-volume assumption is needed for these upper bounds.</p>

<p><em>Proof.</em> Fix the graph and put $v=V(r-1)\ge1$. The supremum mean-exit bound <a href="/tag/331W/">331W</a> gives</p>
<div class="math-display">$$
\sup_{x\in D_r}\mathbf E_xT_r\le2rv
\quad\text{for ordinary walk},\qquad
\sup_{x\in D_r}\mathbf E_x\widehat T_r\le4rv.
$$</div>
<p>The integer block length $m=8rv$ therefore satisfies
$\sup_{x\in D_r}\mathbf P_x(T_r&gt;m)\le1/2$ for either walk. Applying the Markov property successively at multiples of $m$ gives
$\sup_x\mathbf P_x(T_r&gt;km)\le2^{-k}$. Thus, for every real $s\ge0$,</p>
<div class="math-display">$$
\mathbf P_o(T_r&gt;s)
\le2\exp\!\left(-\frac{(\log2)s}{8rV(r-1)}\right).
$$</div>
<p>Write $c_0=(\log2)/8$. For $u\ge1$ split according to whether $V(r)&gt;ur^2$. On the complementary event $V(r-1)\le ur^2$, so</p>
<div class="math-display">$$
\overline{\mathbf P}(T_r&gt;tr^3)
\le C_Ve^{-c_Vu}+2e^{-c_0t/u}.
$$</div>
<p>Taking $u=\sqrt t$ proves the tail estimate for $t\ge1$. It gives a uniform exponential moment of $\sqrt{T_r/r^3}$ for a sufficiently small coefficient. The volume hypothesis gives one for $V(r)/r^2$ as well. Cauchy–Schwarz, after reducing the coefficient, gives the joint exponential bound; independence is not used.</p>
<p>Finally, tail integration bounds
$\overline{\mathbf E}(T_r/r^3)^q$ by a constant times
$1+c^{-2q}\Gamma(2q+1)$. This proves all positive moments and, by the usual gamma-function bound, the stated $q^2$ growth for $q\ge1$. $\square$</p>

## The range when a sphere is first reached {#section-range-at-exit}

<p>Let $W_{T_r}=\{X_0,\ldots,X_{T_r}\}$ include the first vertex reached on $S(r)$, and set $A_{T_r}=\sum_{y\in W_{T_r}}\pi(y)$. Unlike a range at a fixed time, this set is always contained in $B(r)$. We can therefore control its upper tail directly by volume.</p>

<a id="tag-RA7K" data-assertion="theorem" data-title="Lower-volume and resistance tails control the small range at intrinsic exit"></a>
<p>Assume the lower-volume and lower-resistance tails of Z0P0, with resistance exponent $\beta&gt;0$. Put</p>
<div class="math-display">$$\kappa_* = \frac{\beta}{3\beta+2}.$$</div>
<p>For ordinary or lazy walk there is $C&lt;\infty$ such that</p>
<div class="math-display">$$
\overline{\mathbf P}(A_{T_r}\le\varepsilon r^2)
\le C\varepsilon^{\kappa_*}
\qquad(r\ge1,\ 0&lt;\varepsilon\le1).
$$</div>
<p>In particular, $\sup_{r\ge1}\overline{\mathbf E}(r^2/A_{T_r})^q&lt;\infty$ for $0&lt;q&lt;\kappa_*$. The assertion does not require an upper-volume tail or a degree bound.</p>

<p><em>Proof.</em> Put $k=\kappa_*^{-1}=3+2/\beta$. It is enough to consider $r\ge r_0$ and small $\varepsilon$; if $r&lt;r_0$, the event is empty when $\varepsilon r^2&lt;1$, and otherwise its probability is bounded by a constant times $\varepsilon^{\kappa_*}$. Suppose likewise that $\varepsilon r^2\ge1$, and set</p>
<div class="math-display">$$
h=(256\varepsilon)^{-1/k},\qquad
s=\left\lfloor\frac{r}{4h^{1+1/\beta}}\right\rfloor.
$$</div>
<p>Take $\varepsilon$ small enough that $h\ge2$. The nonempty-event condition gives $r\ge16h^{k/2}$, so</p>
<div class="math-display">$$
1\le s&lt;r,\qquad
s\ge\frac{r}{8h^{1+1/\beta}}.
$$</div>
<p>On the environment event</p>
<div class="math-display">$$
F=\{\mathcal R(r)&gt;r/h^{1/\beta},\quad V(s)&gt;s^2/h\},
\qquad \mu(F^c)\le(c_R+a)/h,
$$</div>
<p>one has $s/\mathcal R(r)\le1/(4h)$. Let $M$ be the degree mass in $B(s)$ missed before $T_r$. The hitting estimate <a href="/tag/LCUN/">LCUN</a>, summed over this ball, gives</p>
<div class="math-display">$$
\mathbf E_oM\le
\frac{s}{\mathcal R(r)-s}V(s),\qquad
\mathbf P_o(M\ge V(s)/2)\le\frac{2}{4h-1}\le\frac1h
\quad\text{on }F.
$$</div>
<p>No independence of the individual missing-vertex events is used. If $F$ holds and less than half the smaller ball is missed, then</p>
<div class="math-display">$$
A_{T_r}&gt;\frac{V(s)}2&gt;\frac{s^2}{2h}
\ge\frac{r^2}{128h^{3+2/\beta}}
=2\varepsilon r^2.
$$</div>
<p>The lower-tail event is therefore contained in the two exceptional events, of total probability at most $(a+c_R+1)/h$. This proves the claimed power. Enlarging the constant covers the remaining $\varepsilon\le1$. Integrating the tail of $r^2/A_{T_r}$ proves the negative-moment bound. Under the holding-time coupling the lazy walk visits exactly the same vertex set at its own exit, so its stopped range has the same law. $\square$</p>

## Exit-time and stopped-range moments on incipient clusters {#section-iic-stopped-moments}

<a id="tag-OBBT" data-assertion="corollary" data-title="Finite-triangle incipient limits have all positive exit-time and stopped-range moments with uniform exponential bounds"></a>
<p>Let $\mu$ be either incipient cylinder limit of IXCJ, retaining finite critical triangle and the fixed-shift ratio hypothesis in the distant-point case. Write $N_{T_r}=|W_{T_r}|$. For ordinary and lazy walk, with the walk's own exit time in each case,</p>
<div class="math-display">$$
\begin{aligned}
\overline{\mathbf E}T_r^p&\asymp_p r^{3p}
&&(-1/47&lt;p&lt;\infty),\\
\overline{\mathbf E}N_{T_r}^{\,p}&\asymp_p r^{2p},\qquad
\overline{\mathbf E}A_{T_r}^{\,p}\asymp_p r^{2p}
&&(-1/7&lt;p&lt;\infty).
\end{aligned}
$$</div>
<p>The comparison constants may depend on the model and on $p$, but not on $r\ge1$. More precisely, for some $c,C,\eta&gt;0$,</p>
<div class="math-display">$$
\begin{aligned}
\overline{\mathbf P}(T_r&gt;u r^3)&\le Ce^{-c\sqrt u},&
\overline{\mathbf P}(N_{T_r}&gt;u r^2)&\le Ce^{-cu}
&& (u\ge1),\\
\overline{\mathbf P}(T_r\le\varepsilon r^3)&\le C\varepsilon^{1/47},&
\overline{\mathbf P}(N_{T_r}\le\varepsilon r^2)&\le C\varepsilon^{1/7}
&& (0&lt;\varepsilon\le1),
\end{aligned}
$$</div>
<div class="math-display">$$
\sup_{r\ge1}\overline{\mathbf E}
\exp\!\left[\eta\left(\sqrt{T_r/r^3}+A_{T_r}/r^2\right)\right]&lt;\infty.
$$</div>
<p>In particular, every joint positive moment of the two normalized stopped observables is uniformly bounded.</p>

<p><em>Proof.</em> The exponential degree-volume bound checked in <a href="/tag/PSNV/">PSNV</a> supplies VI2M. The geometric estimates used in <a href="/tag/G85Z/">G85Z</a> supply RA7K with $\beta=1/2$, hence $\kappa_*=1/7$. Also $A_{T_r}\le V(r)$, since the walk stays in $B(r)$ up to and including its first hit of $S(r)$. This gives its exponential upper tail and allows replacement of $V(r)$ by $A_{T_r}$ in VI2M's joint bound.</p>
<p>The already proved fast-exit estimate <a href="/tag/YWT9/">YWT9</a> gives the small exit-time tail. Integrating the two tails yields every positive exit moment and the negative moments above $-1/47$. For stopped range the corresponding integration gives the interval $(-1/7,\infty)$. In each case choose a fixed small lower cutoff and large upper cutoff so that the normalized variable lies between them with probability at least one half. This gives the lower comparison for each real power in the stated range, including the negative powers. The case $p=0$ is immediate.</p>
<p>Finally $N_{T_r}\le A_{T_r}\le2dN_{T_r}$. Thus the probability and moment estimates pass to cardinality, reversing the inequalities for negative powers and changing only constants. Hölder or the joint exponential bound supplies all joint positive moments. $\square$</p>
<p>These are statements at an intrinsic exit time. They do not supply the still-missing upper means of displacement and range at a deterministic time, identify the incipient constructions, or assert optimal tail powers or divergence at the excluded negative endpoints. No earlier tagged statement or source correction is changed.</p>


## All inverse moments of the maximum {#section-inverse-maximum}

<p>The slow-exit estimate also controls how small the maximum distance can be at a fixed time. This maximum, unlike the distance at the final time, remembers an excursion even after the walk has returned.</p>

<a id="tag-ZY62" data-assertion="theorem" data-title="An exponential volume tail gives exponential integrability of the inverse intrinsic maximum"></a>
<p>Under the exponential degree-volume hypothesis of <a href="/tag/VI2M/">VI2M</a>, put $M_n=(1+L_n)/n^{1/3}$. There are $c,C,\theta&gt;0$ such that, for either ordinary or lazy walk,</p>
<div class="math-display">$$
\overline{\mathbf P}(M_n\le\varepsilon)
\le C\exp(-c\varepsilon^{-3/2})
\qquad(n\ge1,\ 0&lt;\varepsilon\le1),
$$</div>
<div class="math-display">$$
\sup_{n\ge1}\overline{\mathbf E}\exp(\theta M_n^{-3/2})&lt;\infty.
$$</div>
<p>In particular, $\sup_n\overline{\mathbf E}M_n^{-q}&lt;\infty$ for every $q&gt;0$, and $\|M_n^{-1}\|_q\le Cq^{2/3}$ for $q\ge1$. No lower-volume or resistance hypothesis is needed.</p>
<p><em>Proof.</em> If $\varepsilon n^{1/3}&lt;1$, the event is empty. Otherwise let $r=\lfloor\varepsilon n^{1/3}\rfloor\ge1$. On that event the integer $L_n$ is at most $r-1$, so $T_r&gt;n$. Since $r\le\varepsilon n^{1/3}$, VI2M gives</p>
<div class="math-display">$$
\overline{\mathbf P}(M_n\le\varepsilon)
\le\overline{\mathbf P}(T_r&gt;n)
\le C\exp\!\left(-c\sqrt{n/r^3}\right)
\le C\exp(-c\varepsilon^{-3/2}).
$$</div>
<p>Thus $M_n^{-3/2}$ has a uniform exponential upper tail above one, proving the exponential moment for $\theta&lt;c$. Integrating the tail of $M_n^{-1}$ bounds its $q$th moment by a constant times $1+c^{-2q/3}\Gamma(1+2q/3)$, and gives the stated growth. The same argument uses the lazy walk's own maximum and exit time. $\square$</p>

## A sharper lower tail for range at a fixed time {#section-improved-range-lower-tail}

<p>A walk that exits a smaller ball before time $n$ has already accumulated the range at that exit. The exponential slow-exit estimate makes the error in this comparison small enough to retain the stopped-range exponent, at the cost of a logarithmic factor.</p>

<a id="tag-GCYB" data-assertion="theorem" data-title="Exponential volume tails transfer the stopped-range lower exponent to fixed time with a logarithmic loss"></a>
<p>Assume VI2M's exponential upper-volume tail and <a href="/tag/RA7K/">RA7K</a>'s lower-volume and lower-resistance tails. Write $\kappa_*=\beta/(3\beta+2)$. For ordinary and lazy walk,</p>
<div class="math-display">$$
\overline{\mathbf P}(A_n\le\varepsilon n^{2/3})
\le C\varepsilon^{\kappa_*}
\bigl(1+\log(1/\varepsilon)\bigr)^{4\kappa_*/3}
\qquad(n\ge1,\ 0&lt;\varepsilon\le1).
$$</div>
<p>Consequently $\sup_n\overline{\mathbf E}(n^{2/3}/A_n)^q&lt;\infty$ for every $0&lt;q&lt;\kappa_*$. These conclusions concern degree range and require no degree bound.</p>
<p><em>Proof.</em> Fix $K\ge1$ large enough that $cK\ge\kappa_*$, where $c$ is the slow-exit constant in VI2M. For small $\varepsilon&gt;0$, put</p>
<div class="math-display">$$
\ell=1+\log(1/\varepsilon),\qquad
r=\left\lfloor\frac{n^{1/3}}{(K\ell)^{2/3}}\right\rfloor.
$$</div>
<p>The lower-tail event is empty if $\varepsilon n^{2/3}&lt;1$. Otherwise $n^{1/3}\ge\varepsilon^{-1/2}$, and, once $\varepsilon$ is below a fixed threshold, the quantity inside the floor is at least two. Hence</p>
<div class="math-display">$$
1\le r,\qquad
\frac{n^{1/3}}{2(K\ell)^{2/3}}\le r
\le\frac{n^{1/3}}{(K\ell)^{2/3}},\qquad
\frac n{r^3}\ge(K\ell)^2.
$$</div>
<p>On $\{T_r\le n\}$ we have $A_n\ge A_{T_r}$. Put $a=\varepsilon n^{2/3}/r^2$. For small enough $\varepsilon$, $a\le4\varepsilon(K\ell)^{4/3}\le1$, so the two estimates give</p>
<div class="math-display">$$
\begin{aligned}
\overline{\mathbf P}(A_n\le\varepsilon n^{2/3})
&\le\overline{\mathbf P}(T_r&gt;n)
 +\overline{\mathbf P}(A_{T_r}\le ar^2)\\
&\le Ce^{-cK\ell}+Ca^{\kappa_*}\\
&\le C\varepsilon^{\kappa_*}\ell^{4\kappa_*/3}.
\end{aligned}
$$</div>
<p>No independence between the exit time and its range is required. Increasing $C$ covers the remaining $\varepsilon\le1$. For $0&lt;q&lt;\kappa_*$, the inverse-moment integral converges because</p>
<div class="math-display">$$
\int_1^\infty x^{q-1-\kappa_*}(1+\log x)^{4\kappa_*/3}\,dx&lt;\infty.
$$</div>
<p>All inclusions and estimates apply to the lazy walk at its own time $n$. $\square$</p>

## Inverse moments on the incipient limits {#section-iic-inverse-moments}

<a id="tag-PDSN" data-assertion="corollary" data-title="Finite-triangle incipient limits have all inverse maximum moments and an improved inverse range interval"></a>
<p>Let $\mu$ be either incipient cylinder limit of IXCJ, with finite critical triangle and the stated fixed-shift ratio hypothesis for distant-point conditioning. For ordinary and lazy walk, uniformly in integers $n\ge1$,</p>
<div class="math-display">$$
\begin{aligned}
\overline{\mathbf E}(1+L_n)^p&\asymp_p n^{p/3}
&&(-\infty&lt;p&lt;3/47),\\
\overline{\mathbf E}N_n^p&\asymp_p n^{2p/3},\qquad
\overline{\mathbf E}A_n^p\asymp_p n^{2p/3}
&&(-1/7&lt;p&lt;3/94).
\end{aligned}
$$</div>
<p>The strengthened probability bounds are</p>
<div class="math-display">$$
\overline{\mathbf P}(1+L_n\le\varepsilon n^{1/3})
\le C\exp(-c\varepsilon^{-3/2}),
$$</div>
<div class="math-display">$$
\overline{\mathbf P}(N_n\le\varepsilon n^{2/3})
\le C\varepsilon^{1/7}(1+\log(1/\varepsilon))^{4/21}
\qquad(0&lt;\varepsilon\le1).
$$</div>
<p>The exponential inverse-maximum moment in ZY62 also holds. Constants may depend on the model and, for moment comparisons, on $p$; no endpoint is included.</p>
<p><em>Proof.</em> The exponential volume tail in <a href="/tag/PSNV/">PSNV</a> supplies ZY62. Together with the lower-volume and resistance estimates checked in <a href="/tag/G85Z/">G85Z</a>, it supplies GCYB with $\beta=1/2$, so $\kappa_*=1/7$. Since $N_n\le A_n\le2dN_n$, the range tail transfers to cardinality, enlarging the constant for the bounded interval where $2d\varepsilon&gt;1$.</p>
<p>ZY62 and GCYB give the new inverse-moment upper bounds. The positive-moment upper bounds remain those of <a href="/tag/YWT9/">YWT9</a> and PSNV. The earlier two-sided tightness puts each normalized observable in a fixed compact subinterval of $(0,\infty)$ with probability at least one half. Its $p$th power on that interval gives the lower comparison for every fixed $p$ in the displayed ranges. For $p=0$ the comparison is exact. $\square$</p>
<p>The inverse-maximum conclusion does not extend in this form to the position at time $n$. For ordinary walk, G85Z's return lower bound gives $\overline{\mathbf E}(1+d(o,X_{2n}))^{-q}\ge c n^{-2/3}$, so an upper bound of order $n^{-q/3}$ is impossible when $q&gt;2$. The present conclusions also leave the positive first moments of displacement and fixed-time range open; the logarithmic loss does not establish the inverse-range endpoint $p=-1/7$.</p>



## Energy bounds without a parity restriction {#section-adjacent-kernel-energy}

<p>The linear small-displacement bound in 5QU6 uses only the first volume moment. A second volume moment gives a quadratic bound. The extra information comes from controlling the variation of the kernel across the ball. For ordinary walk, averaging two adjacent times removes the obstruction from the negative part of the spectrum.</p>

<a id="tag-05B3" data-assertion="proposition" data-title="Averaging adjacent ordinary kernels gives a spatial energy bound at every time"></a>
<p>On an infinite connected locally finite simple graph with unit conductances, retain the degree measure $\pi$, intrinsic balls $B(r)$, volume $V(r)$ and degree-normalized kernels above. Put $Q=(I+P)/2$, $h=\mathbf1_{\{o\}}/\pi(o)$ and, for $n\ge1$,</p>
<div class="math-display">$$
m=\lfloor n/2\rfloor,\qquad A_n=q_{2m}(o,o),\qquad
f_n=P^nQh=\tfrac12\bigl(q_n(o,\cdot)+q_{n+1}(o,\cdot)\bigr).
$$</div>
<p>With $\mathcal E(f)=\sum_{\{x,y\}}(f(x)-f(y))^2$, the sum being over edges,</p>
<div class="math-display">$$
\tfrac12q_{2\lceil n/2\rceil}(o,o)\le f_n(o)\le A_n,
\qquad \mathcal E(f_n)\le\frac{A_n}{n+1}.
$$</div>
<p>Consequently, for every integer $r\ge0$,</p>
<div class="math-display">$$
\mathbf P_o(X_n\in B(r))
\le2V(r)\left(A_n+\sqrt{\frac{rA_n}{n+1}}\right).
$$</div>
<p>For lazy walk $Y$, put $\widehat A_n=\widehat q_n(o,o)$. Then</p>
<div class="math-display">$$
\mathbf P_o(Y_n\in B(r))
\le V(r)\left(\widehat A_n+\sqrt{\frac{2r\widehat A_n}{n+1}}\right).
$$</div>
<p><em>Proof.</em> Let $\nu$ be the spectral measure of the self-adjoint contraction $P$ at $h$ in $\ell^2(\pi)$. Its support is contained in $[-1,1]$, and $q_k(o,o)=\int t^k\,d\nu(t)$. Since $n\ge2m$ and $0\le(1+t)/2\le1$,</p>
<div class="math-display">$$
f_n(o)=\int t^n\frac{1+t}{2}\,d\nu(t)
\le\int |t|^{2m}\,d\nu(t)=A_n.
$$</div>
<p>The lower bound follows from nonnegativity of the two diagonal kernels: one of their times is $2\lceil n/2\rceil$. The energy identity gives</p>
<div class="math-display">$$
\begin{aligned}
\mathcal E(f_n)
&=\frac14\int(1-t)(1+t)^2t^{2n}\,d\nu(t)\\
&\le\frac12\int(1-t^2)|t|^{2n}\,d\nu(t)
\le\frac{A_n}{2(n-m+1)}
\le\frac{A_n}{n+1}.
\end{aligned}
$$</div>
<p>For the middle inequality use $(1-s)s^{n-m}\le1/(n-m+1)$ on $0\le s\le1$. Along a shortest path from $o$ to $y$, Cauchy–Schwarz gives</p>
<div class="math-display">$$
|f_n(y)-f_n(o)|\le\sqrt{d_G(o,y)\mathcal E(f_n)}.
$$</div>
<p>Reversibility identifies $P^kh(y)$ with $q_k(o,y)$, and $q_n(o,y)\le2f_n(y)$. Summing over $B(r)$ proves the ordinary bound. For $\widehat f_n=Q^nh$, the spectral calculation in KGNK gives $\mathcal E(\widehat f_n)\le2\widehat A_n/(n+1)$. Apply the same path estimate and sum. $\square$</p>

## Quadratic small-displacement probabilities {#section-quadratic-small-displacement}

<a id="tag-9JIV" data-assertion="theorem" data-title="A second volume moment gives quadratic annealed small-ball probabilities"></a>
<p>Assume VFZN's linear lower-volume tail and, for some $K&lt;\infty$,</p>
<div class="math-display">$$
\mathbb E_\mu[V(r)^2]\le Kr^4\qquad(r\in\mathbb Z_{\ge1}).
$$</div>
<p>For ordinary or lazy walk $Z$ under the joint law, there is $C&lt;\infty$ such that</p>
<div class="math-display">$$
\overline{\mathbf P}\bigl(d_G(o,Z_n)\le r\bigr)
\le\min\{1,C(r+1)^2(n+1)^{-2/3}\}
\qquad(n\ge1,\ r\in\mathbb Z_{\ge0}).
$$</div>
<p>If the lower-resistance tail in Z0P0 also holds, there are $c_0,c_1&gt;0$ and $n_0&lt;\infty$ such that, for both walks,</p>
<div class="math-display">$$
\overline{\mathbf P}\bigl(d_G(o,Z_n)\le r\bigr)
\ge c_1r^2(n+1)^{-2/3}
\qquad(n\ge n_0,\ 1\le r\le c_0(n+1)^{1/3},\ r\in\mathbb Z).
$$</div>
<p>The lower bound starts at radius one. On a bipartite graph an ordinary walk cannot return to the root at an odd time.</p>
<p><em>Proof.</em> Write $L=(n+1)^{1/3}$. For either $A=A_n$ or $A=\widehat A_n$ in 05B3, VFZN gives</p>
<div class="math-display">$$
\mathbb E_\mu A\le CL^{-2},\qquad
\mathbb E_\mu A^2\le CL^{-4}.
$$</div>
<p>For $A_n$, the even time $2\lfloor n/2\rfloor$ is comparable to $n$ when $n\ge2$; at $n=1$ use $q_0(o,o)=1/\pi(o)\le1$. Also $V(0)\le V(1)$. Cauchy–Schwarz in the environment therefore yields</p>
<div class="math-display">$$
\mathbb E_\mu[V(r)A]\le C(r+1)^2L^{-2},\qquad
\mathbb E_\mu[V(r)\sqrt A]\le C(r+1)^2L^{-1}.
$$</div>
<p>The first estimate in each of 05B3's probability bounds has the required order. The second is at most $C(r+1)^2L^{-2}\sqrt{r/L}$, hence has the same bound when $r\le L$. When $r&gt;L$, use the bound one. This proves the upper estimate.</p>
<p>For the lower estimate, the second volume moment implies the first-moment hypothesis of Z0P0. Its two-sided return moments, followed by Paley–Zygmund, give $a,p&gt;0$ such that for all sufficiently large $n$,</p>
<div class="math-display">$$
\mu\bigl(q_{2\lceil n/2\rceil}(o,o)\ge aL^{-2}\bigr)\ge p,
\qquad
\mu\bigl(\widehat A_n\ge aL^{-2}\bigr)\ge p.
$$</div>
<p>Choose $b$ large enough that $\mu(A_n&gt;bL^{-2})$ and $\mu(\widehat A_n&gt;bL^{-2})$ are at most $p/4$, uniformly in these $n$. Choose $\varepsilon&gt;0$ small enough that $\mu(V(s)\le\varepsilon s^2)\le p/4$ for every integer $s\ge1$. No independence is needed: the corresponding three conditions hold together with probability at least $p/2$.</p>
<p>Consider ordinary walk first. On this intersection, 05B3 gives $f_n(o)\ge(a/2)L^{-2}$ and $\mathcal E(f_n)\le bL^{-5}$. If $s\le c_0L$ and $c_0$ is sufficiently small, then throughout $B(s)$,</p>
<div class="math-display">$$
f_n(y)\ge\frac a2L^{-2}-\sqrt{bsL^{-5}}
\ge\frac a4L^{-2}.
$$</div>
<p>For an integer $r\ge2$, take $s=r-1$. Every step ending in $B(r-1)$ starts in $B(r)$, so</p>
<div class="math-display">$$
\sum_{y\in B(r-1)}\pi(y)f_n(y)
=\tfrac12\left[\mathbf P_o(X_n\in B(r-1))+
\mathbf P_o(X_{n+1}\in B(r-1))\right]
\le\mathbf P_o(X_n\in B(r)).
$$</div>
<p>On the chosen event the left side is at least $(a\varepsilon/4)(r-1)^2L^{-2}$. Average and use $r-1\ge r/2$. At radius one, an even-time root return already gives the lower bound. At an odd time, $X_{n+1}=o$ implies $X_n\in B(1)$, and the next even-time return gives it. These averaged return bounds follow from Z0P0 and $\pi(o)\ge1$.</p>
<p>For lazy walk use the event $aL^{-2}\le\widehat A_n\le bL^{-2}$ and $V(r)&gt;\varepsilon r^2$. The energy is at most $2bL^{-5}$. Decreasing $c_0$ if necessary makes $\widehat q_n(o,y)\ge(a/2)L^{-2}$ on $B(r)$ whenever $1\le r\le c_0L$. Summation and averaging finish the proof. $\square$</p>

## The inverse-position moment transition {#section-iic-inverse-position-transition}

<a id="tag-FPDW" data-assertion="corollary" data-title="Inverse intrinsic position moments on the incipient limits have a sharp transition at order two"></a>
<p>Let $\mu$ be either incipient cylinder limit covered by IXCJ: assume finite critical triangle, and retain the stated ratio hypothesis for the distant-point construction. Let $Z$ be ordinary or lazy walk from the root. For each fixed $q&gt;0$, uniformly over integers $n\ge1$,</p>
<div class="math-display">$$
\overline{\mathbf E}\bigl[(1+d_G(o,Z_n))^{-q}\bigr]
\asymp_q
\begin{cases}
(n+1)^{-q/3},&0&lt;q&lt;2,\\
(n+1)^{-2/3}\log(n+2),&q=2,\\
(n+1)^{-2/3},&q&gt;2.
\end{cases}
$$</div>
<p>The constants may depend on the fixed model and limiting law. In particular, combining this result with YWT9 gives</p>
<div class="math-display">$$
\overline{\mathbf E}\bigl[(1+d_G(o,Z_n))^p\bigr]
\asymp_p(n+1)^{p/3}
\qquad(-2&lt;p&lt;3/47).
$$</div>
<p>These are bounds by positive constant multiples, not asymptotic equivalents.</p>
<p><em>Proof.</em> G85Z verifies the lower-volume and resistance hypotheses for these limits. The exponential degree-volume upper tail used in PSNV gives $\mathbb E_\mu V(r)^2\le Cr^4$ for integer $r\ge1$, by integration. Thus 9JIV applies.</p>
<p>Put $D_n=1+d_G(o,Z_n)$ and $L=(n+1)^{1/3}$. Tonelli gives the exact identity</p>
<div class="math-display">$$
\overline{\mathbf E}D_n^{-q}
=q\int_1^\infty t^{-q-1}\overline{\mathbf P}(D_n\le t)\,dt.
$$</div>
<p>The upper bound in 9JIV implies $\overline{\mathbf P}(D_n\le t)\le\min\{1,Ct^2/L^2\}$. Splitting the integral at $L$ bounds it by</p>
<div class="math-display">$$
\frac{Cq}{L^2}\int_1^L t^{1-q}\,dt+L^{-q}.
$$</div>
<p>This is of order $L^{-q}$ for $q&lt;2$, $L^{-2}\log L$ for $q=2$, and $L^{-2}$ for $q&gt;2$.</p>
<p>For the matching lower bounds, take $n$ sufficiently large. At radius $\lfloor c_0L\rfloor$, 9JIV gives a fixed positive probability of $D_n\le1+c_0L$, which suffices when $q&lt;2$. When $q=2$, use the lower bound in 9JIV at radius $\lfloor t-1\rfloor$ for $3\le t\le c_0L$. This radius lies between $t/3$ and $c_0L$, so integration gives a positive multiple of $L^{-2}\int_3^{c_0L}t^{-1}\,dt$. When $q&gt;2$, the radius-one lower bound yields</p>
<div class="math-display">$$
\overline{\mathbf E}D_n^{-q}
\ge2^{-q}\overline{\mathbf P}\bigl(d_G(o,Z_n)\le1\bigr)
\ge c_qL^{-2}.
$$</div>
<p>Finally $1\le D_n\le n+1$, for either walk, so the finitely many smaller times can be absorbed into positive constants. The assertion for negative $p$ follows on setting $q=-p$; $p=0$ is immediate and the positive range is YWT9. $\square$</p>
<p>The endpoint logarithm comes from the whole range of radii between one and $n^{1/3}$. Orders above two are instead controlled by returns to a fixed neighbourhood of the root. Averaging adjacent kernels handles this distinction at odd times without asserting an odd-time root return. The positive mean-displacement and mean-range upper bounds, and identification of the incipient constructions, remain separate.</p>



## Visits to the starting point {#section-root-visit-renewal}

<p>Write $\ell_n=\sum_{k=0}^n\mathbf1_{\{Z_k=o\}}$ for the number of visits to the root by time $n$, including time zero. On a fixed graph let $U_n=\mathbf E_o\ell_n$. The return estimates control $U_n$; the following renewal argument transfers that control to $\ell_n$. It also applies to Markov chains that are not reversible.</p>

<a id="tag-Y2C3" data-assertion="theorem" data-title="Root visit counts have exponential upper tails and linear lower tails relative to their fixed-chain mean"></a>
<p>Let $Z$ be a time-homogeneous Markov chain on a countable state space, started at $o$. For every integer $n\ge0$, every $0\le\theta&lt;1$ and every integer $m\ge1$,</p>
<div class="math-display">$$
\mathbf E_o\exp\!\left(\theta\frac{\ell_n}{U_n}\right)
\le\frac1{1-\theta},\qquad
\mathbf P_o(\ell_n\le m)\le\min\left\{1,\frac{e}{1-e^{-1}}\frac m{U_n}\right\}.
$$</div>
<p>Consequently, for each fixed $p&gt;-1$, there are positive constants depending only on $p$ such that</p>
<div class="math-display">$$
c_pU_n^p\le\mathbf E_o\ell_n^p\le C_pU_n^p.
$$</div>
<p>No recurrence assumption is needed.</p>
<p><em>Proof.</em> Put $u_k=\mathbf P_o(Z_k=o)$. For an integer $j\ge1$, order the $j$ visit times in the expansion of $\ell_n^j$. The Markov property gives</p>
<div class="math-display">$$
\mathbf E_o\ell_n^j
\le j!\sum_{0\le t_1\le\cdots\le t_j\le n}
u_{t_1}u_{t_2-t_1}\cdots u_{t_j-t_{j-1}}
\le j!U_n^j.
$$</div>
<p>Repeated times are allowed and contribute $u_0=1$. Removing the constraint that the nonnegative time increments have sum at most $n$ proves the second inequality. Summing the exponential series proves the first assertion.</p>
<p>Let $T$ be the first positive return time, with $T=\infty$ on nonreturn, and put $F(z)=\mathbf E_o[z^T]$, where $z^\infty=0$ for $0&lt;z&lt;1$. Decomposing a return according to the first positive return gives</p>
<div class="math-display">$$
G(z):=\sum_{k\ge0}u_kz^k=\frac1{1-F(z)}.
$$</div>
<p>If $S_m$ is the time of the $m$th positive return, the strong Markov property gives $\mathbf E_o[z^{S_m}]=F(z)^m$, including defective returns. Since $\ell_n\le m$ exactly when $S_m&gt;n$, take $z=e^{-1/(n+1)}$ to obtain</p>
<div class="math-display">$$
\mathbf P_o(\ell_n\le m)
\le\frac{1-F(z)^m}{1-e^{-1}}
\le\frac m{(1-e^{-1})G(z)}
\le\frac{e}{1-e^{-1}}\frac m{U_n}.
$$</div>
<p>The first inequality uses $S_m\ge n+1$ on the event in question; the last uses $G(z)\ge e^{-1}U_n$.</p>
<p>The exponential estimate at $\theta=1/2$ bounds every positive moment by a constant times $U_n^p$. Conversely, $\mathbf E_o\ell_n^2\le2U_n^2$, so Paley–Zygmund gives $\mathbf P_o(\ell_n\ge U_n/2)\ge1/8$, supplying all positive lower bounds. For $p=-q$ with $0&lt;q&lt;1$, put $W=\ell_n/U_n$. The lower-tail estimate, with an integer part when needed, gives $\mathbf P_o(W\le t)\le\min\{1,Ct\}$. Therefore</p>
<div class="math-display">$$
\mathbf E_oW^{-q}
=q\int_0^\infty t^{-q-1}\mathbf P_o(W\le t)\,dt
\le\frac{Cq}{1-q}+1.
$$</div>
<p>Jensen's inequality gives the matching lower bound $\mathbf E_oW^{-q}\ge1$, because $\mathbf E_oW=1$. The case $p=0$ is immediate. $\square$</p>

## A resistance bound for finite-time occupation {#section-root-occupation-resistance}

<a id="tag-7UZM" data-assertion="theorem" data-title="Resistance and an upper volume tail control small root occupation without an inverse-volume assumption"></a>
<p>On an infinite connected locally finite simple graph with unit conductances, let $U_n$ be the mean root visit count for ordinary or lazy walk. For every $n\ge0$ and integer $r\ge1$,</p>
<div class="math-display">$$
U_n\ge\frac{\pi(o)}8
\min\left\{\mathcal R(r),\frac{n+1}{V(r)}\right\}.
$$</div>
<p>Now let the rooted graph have law $\mu$. Suppose there are $C_V,c_V,C_R&gt;0$, an integer $r_0\ge1$ and $0&lt;\beta&lt;2/3$ such that</p>
<div class="math-display">$$
\mu(V(r)&gt;ur^2)\le C_Ve^{-c_Vu}\quad(r\ge1,\ u\ge1),\qquad
\mu(\mathcal R(r)\le r/\lambda)\le C_R\lambda^{-\beta}
\quad(r\ge r_0,\ \lambda&gt;1).
$$</div>
<p>For either walk, uniformly over $n\ge1$ and $0&lt;\varepsilon\le1$,</p>
<div class="math-display">$$
\begin{aligned}
\mu\bigl(U_n\le\varepsilon(n+1)^{1/3}\bigr)
&\le C\varepsilon^{3\beta/2}\bigl(\log(e/\varepsilon)\bigr)^{\beta/2},\\
\overline{\mathbf P}\bigl(\ell_n\le\varepsilon(n+1)^{1/3}\bigr)
&\le C\varepsilon^{3\beta/2}\bigl(\log(e/\varepsilon)\bigr)^{\beta/2}.
\end{aligned}
$$</div>
<p><em>Proof.</em> Start with lazy walk and write $N=n+1$, $z=e^{-1/N}$ and $h=\mathbf1_{\{o\}}/\pi(o)$. Its degree-normalized resolvent is</p>
<div class="math-display">$$
\widehat G(z)=\sum_{k\ge0}z^k\widehat q_k(o,o)
=\langle h,(I-zQ)^{-1}h\rangle_{\ell^2(\pi)}.
$$</div>
<p>Let $g_r$ be the killed Green kernel from 331W and set $f(x)=g_r(o,x)/\mathcal R(r)$ on $D_r$, extending it by zero elsewhere. The voltage characterization gives $f(o)=1$, $0\le f\le1$ and $\mathcal E(f)=1/\mathcal R(r)$. In particular $\|f\|_{\ell^2(\pi)}^2\le V(r)$. Cauchy–Schwarz for the positive operator $I-zQ$ yields</p>
<div class="math-display">$$
\widehat G(z)\ge\frac{\langle h,f\rangle^2}{\langle f,(I-zQ)f\rangle}
\ge\frac1{V(r)/N+1/(2\mathcal R(r))}
\ge\frac12\min\{\mathcal R(r),N/V(r)\}.
$$</div>
<p>Here $1-z\le1/N$ and $I-Q=(I-P)/2$. To return to a finite time horizon, use monotonicity of the lazy diagonal kernel. If $\widehat U_n$ is the lazy mean visit count, then $\widehat q_n(o,o)\le\widehat U_n/(N\pi(o))$, and</p>
<div class="math-display">$$
\sum_{k&gt;n}z^k\widehat q_k(o,o)
\le\frac{\widehat U_n}{N\pi(o)}\frac{e^{-1}}{1-e^{-1/N}}
\le\frac{\widehat U_n}{(e-1)\pi(o)}.
$$</div>
<p>The last inequality follows from $1-e^{-1/N}\ge(1-e^{-1})/N$. Hence $\widehat G(z)\le2\widehat U_n/\pi(o)$, proving the deterministic bound with $1/4$ for lazy walk. For ordinary walk, the binomial expansion gives</p>
<div class="math-display">$$
\widehat U_n
=\sum_{j=0}^nu_j\sum_{k=j}^n2^{-k}\binom{k}{j}
\le2\sum_{j=0}^nu_j=2U_n,
$$</div>
<p>since the corresponding infinite inner sum equals two. This proves the stated constant for both walks.</p>
<p>For the first probabilistic bound put $L=N^{1/3}$ and $K=K_0\log(e/\varepsilon)$, where $K_0\ge1$ is fixed large enough. For sufficiently small $\varepsilon$, uniformly in $L\ge1$, set</p>
<div class="math-display">$$
r=\left\lfloor\frac{L}{8\sqrt{\varepsilon K}}\right\rfloor,
\qquad \lambda=\frac{r}{16\varepsilon L}.
$$</div>
<p>Since $\varepsilon K\to0$, we may ensure $r\ge r_0$, $r\ge L/(16\sqrt{\varepsilon K})$ and $\lambda&gt;1$. If $V(r)\le Kr^2$ and $\mathcal R(r)&gt;r/\lambda=16\varepsilon L$, then $N/V(r)\ge64\varepsilon L$. The deterministic bound and $\pi(o)\ge1$ give $U_n&gt;2\varepsilon L$. A union bound therefore gives</p>
<div class="math-display">$$
\mu(U_n\le\varepsilon L)
\le C_Ve^{-c_VK}+C_R\lambda^{-\beta}
\le C\varepsilon^{3\beta/2}\bigl(\log(e/\varepsilon)\bigr)^{\beta/2},
$$</div>
<p>on taking $c_VK_0\ge3\beta/2$. Enlarging $C$ covers the remaining $\varepsilon\le1$.</p>
<p>Finally put $A=U_n/L$, $a=3\beta/2&lt;1$ and $b=\beta/2$. Conditional on the graph, Y2C3 bounds the small-occupation probability by $\min\{1,C_0\varepsilon/A\}$. For $\delta=C_0\varepsilon&lt;1$, Tonelli gives</p>
<div class="math-display">$$
\mathbb E_\mu\min\{1,\delta/A\}
=\delta\int_\delta^\infty\frac{\mu(A\le t)}{t^2}\,dt
\le C\delta^a\bigl(\log(e/\delta)\bigr)^b.
$$</div>
<p>Indeed, on $[\delta,1]$ bound the logarithm by $\log(e/\delta)$ and integrate $t^{a-2}$; on $[1,\infty)$ use probability at most one. The case $\delta\ge1$ is absorbed into the constant. This proves the second bound. $\square$</p>

## Root local time on the incipient limits {#section-iic-root-local-time}

<a id="tag-ZZC8" data-assertion="theorem" data-title="Incipient root visit counts have fractional moment bounds and almost-sure exponent one third"></a>
<p>Let $\mu$ be either incipient cylinder limit in IXCJ, retaining finite critical triangle and the ratio hypothesis for the distant-point construction. For ordinary or lazy walk and every fixed $-3/4&lt;p&lt;3$,</p>
<div class="math-display">$$
\overline{\mathbf E}\ell_n^p\asymp_p(n+1)^{p/3}
\qquad(n\ge1).
$$</div>
<p>More precisely, for $0&lt;\varepsilon\le1$,</p>
<div class="math-display">$$
\overline{\mathbf P}\bigl(\ell_n\le\varepsilon(n+1)^{1/3}\bigr)
\le C\varepsilon^{3/4}\bigl(\log(e/\varepsilon)\bigr)^{1/4}.
$$</div>
<p>For $\mu$-almost every graph, under its walk law,</p>
<div class="math-display">$$
\lim_{n\to\infty}\frac{\log\ell_n}{\log n}=\frac13,
\qquad
\lim_{m\to\infty}\frac{\log S_m}{\log m}=3
\quad\mathbf P_o\text{-almost surely},
$$</div>
<p>where $S_m$ is the time of the $m$th positive return to $o$.</p>
<p><em>Proof.</em> PSNV supplies the exponential degree-volume tail and G85Z supplies the lower-resistance tail with $\beta=1/2$. Thus 7UZM gives the displayed small-occupation bound. Integrating it proves</p>
<div class="math-display">$$
\overline{\mathbf E}\ell_n^{-q}\le C_q(n+1)^{-q/3}
\qquad(0&lt;q&lt;3/4).
$$</div>
<p>To control positive moments, write $u_k=\mathbf P_o(Z_k=o)$ on each graph. For every $1\le p&lt;3$, G85Z gives $\|u_k\|_{L^p(\mu)}\le C_p(k+1)^{-2/3}$. For ordinary odd times use $u_{2j+1}\le u_{2j}$, which follows from the spectral representation; $u_0=1$ handles the initial time. Minkowski's inequality gives</p>
<div class="math-display">$$
\|U_n\|_{L^p(\mu)}
\le\sum_{k=0}^n\|u_k\|_{L^p(\mu)}
\le C_p(n+1)^{1/3}.
$$</div>
<p>For $0&lt;p&lt;1$, Jensen gives the same upper moment bound. Apply Y2C3 on each graph and then average to obtain the positive upper bounds for $\ell_n$.</p>
<p>Summing G85Z's lower return bounds over even times gives $\overline{\mathbf E}\ell_n\ge c(n+1)^{1/3}$ for ordinary walk, and summing all times gives it for lazy walk. The second-moment upper bound and Paley–Zygmund then give all positive lower moment bounds. For negative powers, Jensen and the upper mean bound give $\overline{\mathbf E}\ell_n^{-q}\ge(\overline{\mathbf E}\ell_n)^{-q}\ge c_q(n+1)^{-q/3}$. The case $p=0$ is immediate.</p>
<p>For the pathwise assertions, fix a graph in IXCJ's full-measure set. Summing its return exponent, using even-time monotonicity for ordinary walk, gives $U_n=n^{1/3+o(1)}$. Y2C3 implies, for every $\eta&gt;0$,</p>
<div class="math-display">$$
\begin{aligned}
\mathbf P_o(\ell_n\ge n^{1/3+\eta})
&\le2\exp\!\left(-\frac{n^{1/3+\eta}}{2U_n}\right),\\
\mathbf P_o(\ell_n\le n^{1/3-\eta})
&\le C\frac{n^{1/3-\eta}}{U_n}.
\end{aligned}
$$</div>
<p>Both are summable along $n=2^j$; if a lower threshold is below one its event is empty. Borel–Cantelli, monotonicity of $\ell_n$ and a countable sequence of $\eta$ tending to zero give the first limit at every time. Recurrence makes all $S_m$ finite, and $S_m\le n$ exactly when $\ell_n\ge m+1$. Inverting the first limit proves the second. $\square$</p>
<p>The bounds at $p=-3/4$ and $p=3$ are not supplied, and neither endpoint is asserted to be optimal. These visit counts concern the root, not the number of distinct vertices visited. The latter's upper mean bound, as well as IIC identification, remains separate.</p>



## Summing return probabilities at the tail exponent {#section-occupation-tail-transfer}

<p>The moment estimates in ZZC8 stop below order three because the return-kernel bound has a cubic tail. That tail can also be summed directly. The argument uses no independence between return probabilities at different times.</p>

<a id="tag-6UKZ" data-assertion="proposition" data-title="A polynomial tail survives summation of return probabilities and passage to root occupation"></a>
<p>Let a time-homogeneous Markov chain on a countable state space, started at $o$, depend measurably on an environment of law $\mu$. Fix $n\ge0$ and $\alpha&gt;1$. Write $u_k=\mathbf P_o(Z_k=o)$, $U_n=\sum_{k=0}^nu_k$ and $\ell_n=\sum_{k=0}^n\mathbf1_{\{Z_k=o\}}$. Suppose deterministic $b_0,\ldots,b_n\ge0$ satisfy</p>
<div class="math-display">$$
\mu(u_k&gt;t)\le\min\{1,(b_k/t)^\alpha\}
\qquad(0\le k\le n,\ t&gt;0).
$$</div>
<p>Put $B=\sum_{k=0}^nb_k$ and $K_\alpha=\alpha/(\alpha-1)$. Then, for $t&gt;0$,</p>
<div class="math-display">$$
\begin{aligned}
\mu(U_n&gt;t)&\le\min\{1,(K_\alpha B/t)^\alpha\},\\
\overline{\mathbf P}(\ell_n&gt;t)
&\le\min\{1,2\Gamma(\alpha+1)(2K_\alpha B/t)^\alpha\}.
\end{aligned}
$$</div>
<p><em>Proof.</em> If an environment event $E$ has probability $\delta&gt;0$, layer-cake integration gives</p>
<div class="math-display">$$
\mathbb E_\mu[u_k\mathbf1_E]
\le\int_0^\infty\min\{\delta,(b_k/s)^\alpha\}\,ds
=K_\alpha b_k\delta^{1-1/\alpha}.
$$</div>
<p>For $b_k=0$ this follows from $u_k=0$ almost surely; otherwise split at $b_k\delta^{-1/\alpha}$. Apply the summed estimate to $E=\{U_n&gt;t\}$. If $\delta&gt;0$, then $t\delta\le K_\alpha B\delta^{1-1/\alpha}$, proving the first bound. Since $u_0=1$, we have $U_n\ge1$ and $B&gt;0$.</p>
<p>By Y2C3, conditional on the environment, $\mathbf P_o(\ell_n&gt;t)\le2\exp(-t/(2U_n))$. For $a&gt;0$, Tonelli and the first bound give</p>
<div class="math-display">$$
\mathbb E_\mu e^{-a/U_n}
=\int_0^\infty\frac{a}{s^2}e^{-a/s}\mu(U_n&gt;s)\,ds
\le(K_\alpha B)^\alpha\int_0^\infty a s^{-\alpha-2}e^{-a/s}\,ds
=\Gamma(\alpha+1)(K_\alpha B/a)^\alpha.
$$</div>
<p>Take $a=t/2$ and average the conditional estimate. $\square$</p>

## Cubic occupation tails and endpoint bounds {#section-iic-occupation-endpoints}

<a id="tag-KMWL" data-assertion="theorem" data-title="Incipient root occupation has a cubic upper tail and explicit endpoint moment bounds"></a>
<p>Let $\mu$ be either incipient cylinder limit in IXCJ, retaining finite critical triangle and the ratio hypothesis in the distant-point case. For ordinary or lazy walk, put $N=n+1$ and $L=N^{1/3}$. Uniformly over integers $n\ge1$ and $\lambda&gt;0$,</p>
<div class="math-display">$$
\mu(U_n&gt;\lambda L)\le\min\{1,C\lambda^{-3}\},\qquad
\overline{\mathbf P}(\ell_n&gt;\lambda L)\le\min\{1,C\lambda^{-3}\}.
$$</div>
<p>In particular the two moment endpoints left aside in ZZC8 satisfy</p>
<div class="math-display">$$
cN\le\overline{\mathbf E}\ell_n^3\le CN\log(eN),\qquad
cN^{-1/4}\le\overline{\mathbf E}\ell_n^{-3/4}
\le CN^{-1/4}\bigl(\log(eN)\bigr)^{5/4}.
$$</div>
<p>More generally, for each fixed $p&gt;3$ and $q&gt;3/4$,</p>
<div class="math-display">$$
\begin{aligned}
c_pN^{p/3}&\le\overline{\mathbf E}\ell_n^p\le C_pN^{p-2},\\
c_qN^{-q/3}&\le\overline{\mathbf E}\ell_n^{-q}
\le C_qN^{-1/4}\bigl(\log(eN)\bigr)^{1/4}.
\end{aligned}
$$</div>
<p>The constants may depend on the model and the displayed fixed orders. These are bounds, not matching endpoint asymptotics; no logarithmic loss is asserted to be necessary.</p>
<p><em>Proof.</em> VFZN and $1\le\pi(o)\le2d$ give $\mu(u_k&gt;t)\le\min\{1,C(k+1)^{-2}t^{-3}\}$ for lazy walk. For ordinary even times use $q_{2j}(o,o)\le2\widehat q_{2j}(o,o)$, and for odd times use $u_{2j+1}\le u_{2j}$ from the spectral representation. Increasing $C$ covers $k=0,1$. Thus 6UKZ applies with $\alpha=3$ and $b_k=C^{1/3}(k+1)^{-2/3}$. Since $\sum_{k=0}^n(k+1)^{-2/3}\le3N^{1/3}$, it gives both tails.</p>
<p>Put $W=\ell_n/L$, so $L^{-1}\le W\le L^2$. For $p\ge3$, the upper tail yields</p>
<div class="math-display">$$
\overline{\mathbf E}W^p
\le1+Cp\int_1^{L^2}t^{p-4}\,dt.
$$</div>
<p>The integral is $2\log L$ at $p=3$, and at most $(L^{2p-6}-1)/(p-3)$ for $p&gt;3$. Multiplying by $L^p$ proves the positive upper bounds.</p>
<p>For inverse moments, ZZC8 gives $\overline{\mathbf P}(W\le t)\le Ct^{3/4}(\log(e/t))^{1/4}$ for $0&lt;t\le1$. The lower cutoff $W\ge L^{-1}$ therefore gives, for $q\ge3/4$,</p>
<div class="math-display">$$
\overline{\mathbf E}W^{-q}
\le1+Cq\int_{1/L}^1t^{-q-1/4}\bigl(\log(e/t)\bigr)^{1/4}\,dt.
$$</div>
<p>At $q=3/4$ substitute $s=\log(e/t)$; the integral is $\frac45[(\log(eL))^{5/4}-1]$. For $q&gt;3/4$, bound the logarithm by $\log(eL)$ and integrate the remaining power to obtain a bound $C_qL^{q-3/4}(\log(eL))^{1/4}$. Multiplication by $L^{-q}$ gives the inverse upper bounds. The positive lower bounds follow from the mean lower bound in ZZC8 and Jensen, since $p\ge3$. The inverse lower bounds follow from its upper mean bound and convexity of $x\mapsto x^{-q}$. $\square$</p>

## Moments of successive return times {#section-iic-return-time-moments}

<a id="tag-2XZU" data-assertion="theorem" data-title="Successive incipient root return times have fractional moments on the cubic scale"></a>
<p>Under the hypotheses of KMWL, let $S_m$ be the time of the $m$th positive return to $o$, for ordinary or lazy walk. Uniformly in integers $m\ge1$,</p>
<div class="math-display">$$
\begin{aligned}
\overline{\mathbf P}(S_m\le t m^3)&\le Ct &&(0&lt;t\le1),\\
\overline{\mathbf P}(S_m&gt;t m^3)&\le Ct^{-1/4}\bigl(\log(et)\bigr)^{1/4} &&(t\ge1).
\end{aligned}
$$</div>
<p>Consequently, for each fixed $-1&lt;p&lt;1/4$,</p>
<div class="math-display">$$
c_pm^{3p}\le\overline{\mathbf E}S_m^p\le C_pm^{3p}.
$$</div>
<p>All these return times are almost surely finite, but $\overline{\mathbf E}S_m^p=\infty$ for every $p\ge1$. No matching moment estimate at $p=-1$, or conclusion for $1/4\le p&lt;1$, is asserted.</p>
<p><em>Proof.</em> Recurrence from IXCJ makes $S_m$ finite almost surely. Put $n=\lfloor tm^3\rfloor$. If $n&lt;m$, the lower-tail event is empty, since $S_m\ge m$. Otherwise $n\ge1$, and</p>
<div class="math-display">$$
\{S_m\le tm^3\}=\{\ell_n\ge m+1\}=\{\ell_n&gt;m\}.
$$</div>
<p>KMWL gives probability at most $C(n+1)/m^3$. Since $n\ge1$ implies $n+1\le2tm^3$, this is at most $2Ct$.</p>
<p>For $t\ge1$, we have $n\ge1$ and $\{S_m&gt;tm^3\}=\{\ell_n\le m\}$. Set $\varepsilon=m/(n+1)^{1/3}$, so $0&lt;\varepsilon&lt;t^{-1/3}\le1$. The function $x^{3/4}(\log(e/x))^{1/4}$ is increasing on $(0,1]$. ZZC8 therefore gives</p>
<div class="math-display">$$
\overline{\mathbf P}(S_m&gt;tm^3)
\le C\varepsilon^{3/4}\bigl(\log(e/\varepsilon)\bigr)^{1/4}
\le Ct^{-1/4}\bigl(\log(et)\bigr)^{1/4}.
$$</div>
<p>Write $H_m=S_m/m^3$. The upper tail is integrable against $t^{p-1}$ for $0&lt;p&lt;1/4$, and the lower tail is integrable against $t^{-q-1}$ near zero for $0&lt;q&lt;1$. These integrals give uniform upper bounds on $\overline{\mathbf E}H_m^p$ in the claimed range. To obtain the lower bounds, choose a fixed small $a&gt;0$ with $Ca\le1/2$, and a fixed large $b$ with $Cb^{-1/4}(\log(eb))^{1/4}\le1/2$. Then $\overline{\mathbf P}(H_m&gt;a)\ge1/2$ and $\overline{\mathbf P}(H_m\le b)\ge1/2$, uniformly in $m$. The first event bounds every positive moment below by $a^p/2$; the second bounds every negative moment below by $b^p/2$. The case $p=0$ is immediate.</p>
<p>To see the divergence, fix an infinite recurrent cluster and write $T=S_1$ and $T_o=\inf\{k\ge0:Z_k=o\}$. Reversibility with respect to $\pi$ gives, for $x\ne o$ and $k\ge1$,</p>
<div class="math-display">$$
\pi(o)\mathbf P_o(Z_k=x,\ T&gt;k)
=\pi(x)\mathbf P_x(T_o=k).
$$</div>
<p>Indeed, reverse each length-$k$ path from $o$ to $x$ with no intervening visit to $o$. Irreducibility and recurrence give $\mathbf P_x(T_o&lt;\infty)=1$. Summing the identity over $k$, and including the initial visit for $x=o$, yields</p>
<div class="math-display">$$
\mathbf E_oT
=\sum_x\mathbf E_o\sum_{k=0}^{T-1}\mathbf1_{\{Z_k=x\}}
=\frac1{\pi(o)}\sum_x\pi(x)=\infty.
$$</div>
<p>The last sum diverges because the cluster is infinite and each degree is at least one. This applies to both transition kernels: their reversible degree measure is the same. Since $S_m\ge T\ge1$, every moment of $S_m$ of order at least one is infinite on each such cluster, hence also after averaging. $\square$</p>



## Degree bias and the environment seen from the walk {#section-iic-degree-bias}

<p>Susceptibility bias has a useful invariance under moving the root inside its cluster. Weighting once more by the root degree makes the environment seen from the walk stationary and reversible. We prove this for susceptibility-biased cylinder limits; no identification with distant-point limits is used.</p>

<a id="tag-K11N" data-assertion="theorem" data-title="Degree-biased susceptibility limits are reversible under the marked walk path"></a>
<p>Consider nearest-neighbour bond percolation on $\mathbb Z^d$. Suppose $\chi(p_j)&lt;\infty$, $\chi(p_j)\to\infty$ and the laws $Q_{p_j}$ from N20X converge on cylinders to $\mu$. Let $\theta_x\omega$ be the translated configuration with $(\theta_x\omega)_{\{u,v\}}=\omega_{\{x+u,x+v\}}$. Define</p>
<div class="math-display">$$
\bar\pi=\mathbb E_\mu\pi(0),\qquad
\mu^\dagger(d\omega)=\frac{\pi(0)}{\bar\pi}\,\mu(d\omega).
$$</div>
<p>Then $1\le\bar\pi\le2d$. Under the joint law that samples $\omega$ from $\mu^\dagger$ and starts ordinary or lazy walk at zero, the process $\theta_{Z_k}\omega$ is stationary. More precisely, for each integer $k\ge0$, the marked path has the same law after the transformation</p>
<div class="math-display">$$
(\omega;0,Z_1,\ldots,Z_k)
\longmapsto
(\theta_{Z_k}\omega;0,Z_{k-1}-Z_k,\ldots,-Z_k).
$$</div>
<p>The marks retain the walk's displacements, even if different translates of a configuration coincide. The densities between $\mu$ and $\mu^\dagger$ are bounded above by $2d$ in both directions.</p>
<p><em>Proof.</em> E22E gives an infinite root cluster under $\mu$, so $1\le\pi(0)\le2d$. For any bounded cylinder function $F(\omega,e)$, where $e$ ranges over the $2d$ nearest neighbours of zero, translation invariance of the underlying product law gives</p>
<div class="math-display">$$
\mathbb E_{Q_p}\sum_{|e|_1=1}\omega_{\{0,e\}}F(\omega,e)
=\mathbb E_{Q_p}\sum_{|e|_1=1}\omega_{\{0,e\}}F(\theta_e\omega,-e).
$$</div>
<p>To verify this, write $Q_p$ with density $|C(0)|/\chi(p)$ and change variables by $\theta_e$ in each summand, then replace $e$ by $-e$. On the open-edge event, $C(e)=C(0)$, so the cluster-size weight is unchanged. Finite susceptibility justifies the bounded integrals.</p>
<p>Both sums are bounded cylinder functions. Pass to the limit along $p_j$, then use the monotone class theorem to obtain the identity for every bounded Borel $F$. After dividing by $\bar\pi$, its left side is</p>
<div class="math-display">$$
\mathbb E_{\mu^\dagger}\sum_{|e|_1=1}
\frac{\omega_{\{0,e\}}}{\pi(0)}F(\omega,e).
$$</div>
<p>Thus the law of the environment and its first marked step is invariant under $(\omega,e)\mapsto(\theta_e\omega,-e)$. This gives stationarity by testing a function of the translated environment alone. Iterating the same balance identity through the Markov transition gives the displayed reversal of every finite marked path. For lazy walk, give the moving steps half their weight and add a holding step of weight one half; its displacement is zero and it reverses to itself. Finally $\pi(0)/\bar\pi$ and its reciprocal both lie in $[1/(2d),2d]$. $\square$</p>

## Range, returns and collisions under a stationary root law {#section-stationary-range-identities}

<a id="tag-VFDK" data-assertion="proposition" data-title="Marked path reversal identifies mean range with first-return tails and controls range through collisions"></a>
<p>Let $\rho$ be a law on nearest-neighbour environments with positive root degree, and suppose its ordinary or lazy marked walk paths are stationary under moving the root and reversible as in K11N. Write $T=\inf\{k\ge1:Z_k=0\}$, allowing $T=\infty$, and put</p>
<div class="math-display">$$
\ell_n(x)=\sum_{i=0}^n\mathbf1_{\{Z_i=x\}},\quad
N_n=|\{Z_0,\ldots,Z_n\}|,\quad
J_n=\sum_x\ell_n(x)^2,\quad N=n+1.
$$</div>
<p>Then</p>
<div class="math-display">$$
\overline{\mathbf E}_\rho N_n
=\sum_{k=0}^n\overline{\mathbf P}_\rho(T&gt;k),\qquad
\overline{\mathbf E}_\rho J_n
=N+2\sum_{k=1}^n(N-k)\mathbb E_\rho u_k,
$$</div>
<p>where $u_k(\omega)=\mathbf P_0^\omega(Z_k=0)$. Deterministically,</p>
<div class="math-display">$$
N_nJ_n\ge N^2,\qquad
J_n=2\sum_{i=0}^n A_{i,n}-N,\qquad
A_{i,n}=\sum_{j=i}^n\mathbf1_{\{Z_j=Z_i\}}.
$$</div>
<p>Under the joint law with initial environment $\rho$, each $A_{i,n}$ has the law of the root occupation $\ell_{n-i}$ with that same initial environment law.</p>
<p><em>Proof.</em> Count a vertex when it is first visited:</p>
<div class="math-display">$$
N_n=\sum_{k=0}^n\mathbf1_{\{Z_k\notin\{Z_0,\ldots,Z_{k-1}\}\}}.
$$</div>
<p>Reverse and recenter the first $k$ steps. The event in the $k$th summand becomes the event that the reversed path avoids its starting point at times $1,\ldots,k$. Marked reversal therefore gives probability $\overline{\mathbf P}_\rho(T&gt;k)$, including the value one at $k=0$. This proves the range identity.</p>
<p>Expanding the squared local times counts all ordered pairs $(i,j)$ with $Z_i=Z_j$. There are $N$ diagonal pairs. For $i&lt;j$, stationarity at time $i$ and the Markov property give probability $\mathbb E_\rho u_{j-i}$, proving the collision identity. Counting upper-triangular pairs instead gives the formula through $A_{i,n}$. The same stationarity and Markov property give its stated marginal law; no independence between the different $A_{i,n}$ is asserted. Finally, Cauchy–Schwarz on the visited vertices gives $N^2=(\sum_x\ell_n(x))^2\le N_nJ_n$. $\square$</p>

## Improved range bounds for susceptibility-biased limits {#section-iic-stationary-range}

<a id="tag-BP8X" data-assertion="theorem" data-title="Susceptibility-biased finite-triangle limits have cubic small-range tails and sublinear mean range"></a>
<p>Assume nearest-neighbour percolation satisfies $\Delta_{p_c}(0)&lt;\infty$, and let $\mu$ be a susceptibility-biased cylinder limit as in IXCJ. For ordinary or lazy walk, uniformly over integers $n\ge1$ and $0&lt;\varepsilon\le1$,</p>
<div class="math-display">$$
\overline{\mathbf P}_\mu\bigl(N_n\le\varepsilon(n+1)^{2/3}\bigr)
\le C\varepsilon^3.
$$</div>
<p>Consequently, for every fixed $0&lt;q&lt;3$,</p>
<div class="math-display">$$
\overline{\mathbf E}_\mu N_n^{-q}\asymp_q(n+1)^{-2q/3},
$$</div>
<p>and the endpoint satisfies</p>
<div class="math-display">$$
c(n+1)^{-2}\le\overline{\mathbf E}_\mu N_n^{-3}
\le C(n+1)^{-2}\log(e(n+1)).
$$</div>
<p>The mean range obeys</p>
<div class="math-display">$$
c(n+1)^{2/3}\le\overline{\mathbf E}_\mu N_n
\le C(n+1)^{3/4}\bigl(\log(e(n+1))\bigr)^{1/4}.
$$</div>
<p>Replacing $N_n$ by the degree-weighted range $A_n$ preserves these estimates up to constants. The cubic lower tail improves the inverse-range interval for this construction. The mean upper bound is still larger than order $n^{2/3}$, and the endpoint logarithm is not claimed necessary. No extension to a distinct distant-point limit is asserted.</p>
<p><em>Proof.</em> Put $N=n+1$ and $\rho=\mu^\dagger$ from K11N. The bounded densities let us transfer nonnegative expectations and probabilities between $\mu$ and $\rho$ at a cost at most $2d$. KMWL and VFDK therefore give, for each $0\le i\le n$ and $t&gt;0$,</p>
<div class="math-display">$$
\overline{\mathbf P}_\rho(A_{i,n}&gt;t)
\le\min\{1,C(n-i+1)t^{-3}\}.
$$</div>
<p>When $i=n$, the variable is one and the same estimate holds after increasing $C$. For any joint environment-and-walk event $E$ of probability $\delta&gt;0$, the event integral used in 6UKZ gives</p>
<div class="math-display">$$
\overline{\mathbf E}_\rho[A_{i,n}\mathbf1_E]
\le\int_0^\infty\min\{\delta,C(n-i+1)t^{-3}\}\,dt
\le C(n-i+1)^{1/3}\delta^{2/3}.
$$</div>
<p>Since $J_n\le2\sum_iA_{i,n}$, summing yields $\overline{\mathbf E}_\rho[J_n\mathbf1_E]\le CN^{4/3}\delta^{2/3}$. Apply this to $E=\{J_n\ge s\}$ to obtain</p>
<div class="math-display">$$
\overline{\mathbf P}_\rho(J_n\ge s)\le C N^4s^{-3}.
$$</div>
<p>On $N_n\le\varepsilon N^{2/3}$, the deterministic inequality in VFDK forces $J_n\ge\varepsilon^{-1}N^{4/3}$. This proves the cubic small-range bound under $\rho$, hence also under $\mu$.</p>
<p>For $W=N_n/N^{2/3}$, integrate $\overline{\mathbf P}_\mu(W\le t)\le\min\{1,Ct^3\}$ against $qt^{-q-1}$. The integral is finite for $0&lt;q&lt;3$. At $q=3$, use $W\ge N^{-2/3}$ and integrate only from that cutoff, giving a bound $C\log(eN)$. For the matching lower bounds, any one positive fractional range moment in PDSN, followed by Markov's inequality, supplies a fixed $b$ with $\overline{\mathbf P}_\mu(N_n\le bN^{2/3})\ge1/2$. On this event $N_n^{-q}\ge b^{-q}N^{-2q/3}$, also at $q=3$.</p>
<p>For the mean upper bound, $T&gt;k$ exactly when $\ell_k\le1$. ZZC8 with $\varepsilon=(k+1)^{-1/3}$ gives, for $k\ge1$,</p>
<div class="math-display">$$
\overline{\mathbf P}_\rho(T&gt;k)
\le C(k+1)^{-1/4}\bigl(\log(e(k+1))\bigr)^{1/4}.
$$</div>
<p>The first identity in VFDK, with the initial summand one, now bounds $\overline{\mathbf E}_\rho N_n$ by $CN^{3/4}(\log(eN))^{1/4}$. Transfer this to $\mu$. For the lower bound, G85Z and the bounded density give $\mathbb E_\rho u_k\le C(k+1)^{-2/3}$, using the even-time spectral comparison at ordinary odd times. The second identity in VFDK gives $\overline{\mathbf E}_\rho J_n\le CN^{4/3}$. Hence Cauchy–Schwarz, or Jensen applied to $1/J_n$, yields</p>
<div class="math-display">$$
\overline{\mathbf E}_\rho N_n
\ge\frac{N^2}{\overline{\mathbf E}_\rho J_n}\ge cN^{2/3}.
$$</div>
<p>Transfer once more to $\mu$. Finally $N_n\le A_n\le2dN_n$ proves the degree-range claims. $\square$</p>
